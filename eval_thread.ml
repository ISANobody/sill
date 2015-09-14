open Base
open Core.Std
open Value
open Vars
open Eval_functor
open Eval_abstract
open Vector_clock

let threadMap : (int list,string list) Map.Poly.t ref = ref Map.Poly.empty
let threadLock = Mutex.create ()

let statsLock = Mutex.create ()
let statsCrit f = if !stats_flag then crit statsLock f
let threadCount = ref 0
let fullThreadCount = ref 0
let focusOps = ref 0
let focusNonOps = ref 0
let forwardMsgs = ref 0
let mainvc = ref 0

module rec Impl_Thread : Impl =
struct
  type communicable = Chan of channel * VectorClock.t option
                    | BoxedChan of Fullsyntax.stype * channel * VectorClock.t option
                    | Term of Thread.t * VectorClock.t option
                    | Val of value * VectorClock.t option
                    | Lab of label * VectorClock.t option
                    | Redir of communicable Squeue.t * VectorClock.t option
                    | Kill (* For affine stuff *)
                    
  and channel = (communicable Squeue.t ref * communicable Squeue.t ref) (* write * read *)
  type proc_local = { id : int list; (* Address in the ancestor relation tree *)
                      childCounter : int ref; (* Number of children spawned so far *)
                      (* What was the last channel we used and in what polarity *)
                      focusCache : [`Send of channel | `Recv of channel] option ref;
                      (* How many times did we communicate along the same channel/polarity *)
                      focusCounter : int ref;
                      unfocusCounter : int ref;
                      numTailbinds : int ref;
                      vecClock : VectorClock.t ref
                    }
  let string_of_comm c =
      match c with
      | Chan _ -> "Chan"
      | Lab (l,_) -> "label "^string_of_label l
      | Val (v,_) -> "val "^string_of_value v
      | Term _ -> "Term"
      | BoxedChan _ -> "BoxedChan"
      | Redir _ -> "Redir"
      | Kill  -> "Kill"
  let setvc vc = function
      | Chan (ch,_) -> Chan (ch,Some vc)
      | Lab (l,_) -> Lab (l,Some vc)
      | Val (v,_) -> Val (v,Some vc)
      | Term (tid,_) -> Term (tid,Some vc)
      | BoxedChan (ty,ch,_) -> BoxedChan (ty,ch,Some vc)
      | Redir (ch,_) -> Redir (ch,Some vc)
      | Kill -> Kill
  let getvc = function
      | Chan (_,Some vc) -> vc
      | Lab (_,Some vc) -> vc
      | Val (_,Some vc) -> vc
      | Term (_,Some vc) -> vc
      | BoxedChan (_,_,Some vc) -> vc
      | Redir (_,Some vc) -> vc
      | _ -> failwith ("getvc pattern match failure")
  let globalControl : channel Squeue.t SM.t ref = ref SM.empty
  let controlLock : Mutex.t = Mutex.create ()
  let log id s = 
    crit threadLock (fun () -> 
    match Map.Poly.find !threadMap id with
    | Some x -> threadMap := Map.Poly.add !threadMap id (x@[s])
    | None -> threadMap := Map.Poly.add !threadMap id [s])
  let print s = print_string s; flush stdout
  let abort (s:string) = prerr_endline s; Pervasives.exit 1
  let init () = at_exit (fun () -> 
    crit threadLock (fun () -> 
    Map.Poly.iter !threadMap (fun ~key:t ~data:ss -> 
                       let ts = intercal string_of_int "." t in 
                       print_endline (ts^": "
                                     ^intercal (fun x -> x) 
                                               ("\n"^String.make (String.length ts+2) ' ') ss)));
    if !stats_flag
    then statsCrit (fun () -> 
      print_endline ("Threads Created:        "^string_of_int !threadCount);
      print_endline ("Logical Threads:        "^string_of_int !fullThreadCount);
      print_endline ("Focusing Opportunities: "^string_of_int !focusOps);
      print_endline ("Writes (w/o forwards):  "^string_of_int (!focusOps + !focusNonOps));
      print_endline ("Forward Messages:       "^string_of_int !forwardMsgs);
      print_endline ("Critical Path Length:   "^string_of_int !mainvc)
      ));
    if !stats_flag
    then Thread_Eval.tail_bind_hook := 
         (fun state -> statsCrit (fun () -> incr state.numTailbinds))
  let procExit state =
      if !stats_flag
      then statsCrit (fun () -> 
             incr threadCount;
             fullThreadCount := !fullThreadCount + 1 + !(state.numTailbinds);
             focusOps := !focusOps + !(state.focusCounter);
             focusNonOps := !focusNonOps + !(state.unfocusCounter);
             mainvc := Vector_clock.VectorClock.get !(state.vecClock) state.id);
      Thread.exit ()
  let mkTerm () = Term (Thread.self (),None)
  let is_Term c = match c with Term (t,_) -> Thread.join t; true | _ -> false
  let valComm v = Val (v,None)
  let getVal c = match c with Val (v,_) -> Some v | _ -> None
  let labComm l = Lab (l,None)
  let getLab c = match c with Lab (l,_) -> Some l | _ -> None
  let chanComm ch = Chan (ch,None)
  let getChan c = match c with Chan (ch,_) -> Some ch | _ -> None
  let boxedChanComm s c = BoxedChan (s,c,None)
  let getBoxedChan c = match c with BoxedChan (s,ch,_) -> Some (s,ch) | _ -> None
  let write_comm state ch c =
    if !stats_flag then 
      Vector_clock.VectorClock.incr1 state.vecClock state.id;
      (match !(state.focusCache) with
      | Some (`Send ch') when physeq ch ch' -> incr state.focusCounter
      | _ -> incr state.unfocusCounter;
             state.focusCache := Some (`Send ch));
    if !stats_flag
      then Squeue.push !(fst ch) (setvc !(state.vecClock) c)
      else Squeue.push !(fst ch) c
  let rec read_comm state ch =
    if !stats_flag then state.focusCache := Some (`Recv ch);
    match Squeue.pop !(snd ch) with
    | Redir (q,Some vc) -> if !stats_flag 
                           then VectorClock.merge1 state.vecClock vc state.id;
                     snd ch := q;
                     read_comm state ch
    | Redir (q,None) -> snd ch := q;
                        read_comm state ch
    | Kill -> procExit state;
              failwith "Unreachable" (* TODO needs to recursively kill it's affine arguments *)
    | c -> 
      if !stats_flag 
      then VectorClock.merge1 state.vecClock (getvc c) state.id;
      c
  let free ch =
    Squeue.push !(fst ch) Kill
  let spawn (env:value SM.t) senv (cenv:Thread_Eval.channel CM.t) (p:Syntax.Core.proc) (c:cvar)
            (state:Thread_Eval.proc_local) =
    let ch : Thread_Eval.channel = (ref (Squeue.create 1),ref (Squeue.create 1))
    in let go = (fun () -> 
         if !eval_trace_flag
         then log state.id 
                  (loc2str (Syntax.Core.locP p)^" bound from "
                  ^intercal string_of_int "." (List.slice state.id 0 (List.length state.id -1)));
         Thread_Eval.eval_proc env senv (CM.add cenv c ch) p state)
       in let _ = Thread.create go ()
          in (snd ch,fst ch)
  let spawnRemote = spawn
  let newChan () = let (c1,c2) = (ref (Squeue.create 1),ref (Squeue.create 1))
                   in ((c1,c2),(c2,c1))
  let forward state chin1 chin2 =
    if !stats_flag
      then (Squeue.push !(fst chin2) (Redir (!(snd chin1),Some !(state.vecClock)));
            Squeue.push !(fst chin1) (Redir (!(snd chin2),Some !(state.vecClock))))
      else (Squeue.push !(fst chin2) (Redir (!(snd chin1),None));
            Squeue.push !(fst chin1) (Redir (!(snd chin2),None)));
    if !stats_flag
    then statsCrit (fun () -> 
           incr threadCount;
           incr forwardMsgs;
           incr forwardMsgs;
           fullThreadCount := !fullThreadCount + 1 + !(state.numTailbinds);
           focusOps := !focusOps + !(state.focusCounter);
           focusNonOps := !focusNonOps + !(state.unfocusCounter);
         );
    Thread.exit ()
  let rec defaultingQueue n =
    match SM.find !globalControl n with
    | Some q -> q
    | None -> crit controlLock (fun () -> 
      (* Test again to make sure we still need to create after the lock has been acquired *)
      match SM.find !globalControl n with
      | Some _ -> ()
      | None -> globalControl := SM.add !globalControl n (Squeue.create 0));
      defaultingQueue n
  let request n = Squeue.pop (defaultingQueue n)
  let register n c = Squeue.push_uncond (defaultingQueue n) c
end
and Thread_Eval : (Evaluator 
  with type channel = (Impl_Thread.communicable Squeue.t ref * Impl_Thread.communicable Squeue.t ref)
   and type proc_local = Impl_Thread.proc_local
              ) = MkEvaluator(Impl_Thread)
