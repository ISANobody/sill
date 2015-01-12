open Base
open Core.Std
open Value
open Vars
open Eval_functor
open Eval_abstract

module TM = Map.Make(Int)

let threadMap : string list TM.t ref = ref TM.empty
let threadLock = Mutex.create ()

let statsLock = Mutex.create ()
let statsCrit f = if !stats_flag then crit statsLock f
let threadCount = ref 0
let fullThreadCount = ref 0
let maxThreadsTemp = ref 0
let maxThreads = ref 0

module rec Impl_Thread : Impl =
struct
  type communicable = Chan of channel
                    | BoxedChan of Fullsyntax.stype * channel
                    | Term of Thread.t
                    | Val of value
                    | Lab of label
                    | Ack
                    | Redir of communicable Squeue.t
                    | Kill (* For affine stuff *)
                    
  and channel = (communicable Squeue.t ref * communicable Squeue.t ref) (* write * read *)
  let string_of_comm c =
      match c with
      | Chan _ -> "Chan"
      | Lab l -> "label "^string_of_label l
      | Val v -> "val "^string_of_value v
      | Ack -> "ack"
      | Term _ -> "Term"
      | BoxedChan _ -> "BoxedChan"
      | Redir _ -> "Redir"
      | Kill  -> "Kill"
  let globalControl : channel Squeue.t SM.t ref = ref SM.empty
  let controlLock : Mutex.t = Mutex.create ()
  let log s = 
    crit threadLock (fun () -> 
    match TM.find !threadMap (Thread.id (Thread.self ())) with
    | Some x -> threadMap := TM.add !threadMap (Thread.id (Thread.self ())) (x@[s])
    | None -> threadMap := TM.add !threadMap (Thread.id (Thread.self ())) [s])
  let print s = print_string s; flush stdout
  let abort (s:string) = prerr_endline s; log s; Pervasives.exit 1
  let init () = at_exit (fun () -> 
    crit threadLock (fun () -> 
    TM.iter !threadMap (fun ~key:t ~data:ss -> 
                       let ts = string_of_int t in 
                       print_endline (ts^": "
                                     ^intercal (fun x -> x) 
                                               ("\n"^String.make (String.length ts+2) ' ') ss)));
    if !stats_flag
    then statsCrit (fun () -> 
         print_endline ("Threads Created:    "^string_of_int !threadCount);
         print_endline ("Logical Threads:    "^string_of_int !fullThreadCount);
         print_endline ("Peak Exec Threads:  "^string_of_int !maxThreads)));
    if !stats_flag
    then Thread_Eval.tail_bind_hook := 
         (fun () -> statsCrit (fun () -> incr fullThreadCount))
  let procExit () =
      decr maxThreadsTemp;
      Thread.exit ()
  let mkTerm () = Term (Thread.self ())
  let is_Term c = match c with Term t -> Thread.join t; true | _ -> false
  let valComm v = Val v
  let getVal c = match c with Val v -> Some v | _ -> None
  let labComm l = Lab l
  let getLab c = match c with Lab l -> Some l | _ -> None
  let chanComm ch = Chan ch
  let getChan c = match c with Chan ch -> Some ch | _ -> None
  let boxedChanComm s c = BoxedChan (s,c)
  let getBoxedChan c = match c with BoxedChan (s,ch) -> Some (s,ch) | _ -> None
  let write_comm ch c =
    let rec read_ack ch = match Squeue.pop !(snd ch) with
                      | Ack -> ()
                      | Redir q -> snd ch := q;
                                   read_ack ch
                      | Kill -> if !eval_trace_flag then log "killed";
                                procExit ();
                                failwith "Unreachable" (* Warning needs to recursively kill 
                                                          it's affine arguments *)
                      | x -> if !eval_trace_flag 
                             then log ("Non-ack for write. BUG. Got: "^string_of_comm x);
                             abort ("Non-ack for write. BUG. Got: "^string_of_comm x)
    in match c with
       | Term _ -> Squeue.push !(fst ch) c
       | _ -> Squeue.push !(fst ch) c;
              read_ack ch
  let rec read_comm ch =
    match Squeue.pop !(snd ch) with
    | Term t -> Term t
    | Redir q -> snd ch := q;
                 read_comm ch
    | Kill -> if !eval_trace_flag then log "killed";
              procExit ();
              failwith "Unreachable" (* Warning needs to recursively kill it's affine arguments *)
    | c -> Squeue.push !(fst ch) Ack;
           c
  let free ch =
    Squeue.push !(fst ch) Kill
  let spawn (env:value SM.t) senv (cenv:Thread_Eval.channel CM.t) (p:Syntax.Core.proc) (c:cvar) =
    let ch : Thread_Eval.channel = (ref (Squeue.create 1),ref (Squeue.create 1))
    and ti = Thread.id (Thread.self ())
    in let go = (fun () -> 
         statsCrit (fun () -> incr threadCount;
                              incr fullThreadCount;
                              incr maxThreadsTemp;
                              if !maxThreadsTemp > !maxThreads
                              then maxThreads := !maxThreadsTemp);
         if !eval_trace_flag
         then log (loc2str (Syntax.Core.locP p)^" bound from "^string_of_int ti);
         Thread_Eval.eval_proc env senv (CM.add cenv c ch) p)
       in let _ = Thread.create go ()
          in (snd ch,fst ch)
  let spawnRemote = spawn
  let newChan () = let (c1,c2) = (ref (Squeue.create 1),ref (Squeue.create 1))
                   in ((c1,c2),(c2,c1))
  let forward chin1 chin2 =
    decr maxThreadsTemp;
    Squeue.push !(fst chin2) (Redir !(snd chin1));
    Squeue.push !(fst chin1) (Redir !(snd chin2));
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
and Thread_Eval : (Evaluator with type channel = (Impl_Thread.communicable Squeue.t ref *
Impl_Thread.communicable Squeue.t ref)) = MkEvaluator(Impl_Thread)
