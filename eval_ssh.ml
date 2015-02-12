open Base
open Core.Std
open Value
open Vars
open Eval_functor
open Eval_abstract
open Catqueue

(* Instead of PID's we identify processes by their location in the ancestry tree *)
let ancestors = ref [0]
let procNum = ref 0

let errorLock = Mutex.create ()

let curThread () = intercal string_of_int ":" !ancestors

(* Some auxiliary functions to make sure we flush *)

let realOut (c:out_channel) (w:'a Bin_prot.Type_class.writer) (d:'a) : unit = 
Bigstring.really_output c (Bin_prot.Utils.bin_dump ~header:true
                                            w d);
            flush c

let realIn (c:in_channel) (w:'a Bin_prot.Type_class.reader) : 'a = 
  Bin_prot.Utils.bin_read_stream ~read:(fun t ~pos:p ~len:l -> Bigstring.really_input c ~pos:p ~len:l t) w

module IM = Map.Make(Int)

(* This module extends the regular interface with auxiliary functions we need visible in
   sshstub.ml *)
module type SSH_Impl = 
sig 
  include Impl
  val unsanitieze_chans : int CM.t -> channel CM.t
end

module rec Impl_SSH : SSH_Impl =
struct
  let log _ s = crit errorLock (fun () -> prerr_endline (curThread ()^" "^s))
  let print s = crit errorLock (fun () -> prerr_endline s; flush stderr)
  let abort s = failwith "ssh-abort unimplemented"
  let free _ = failwith "ssh-free unimplemented"
  type communicable = Term 
                    | Ack 
                    | Val of value
                    | Lab of label
                    | Ch of channel
  and channel = Chan of communicable Catqueue.t * communicable Catqueue.t
  (* Channels aren't serializeable so we can't just directly wrap with redirection info *)
  type commWrapper = WrapTerm of int
                   | WrapAck of int
                   | WrapLab of int * label
                   | WrapCh of int * int
                   | WrapVal of int * value with bin_io

  let string_of_comm cin =
    match cin with
    | Term -> "Term"
    | Ack -> "Ack"
    | Val v -> string_of_value v
    | Lab l -> string_of_label l
    | Ch _ -> "Ch"
  let string_of_commWrapper cin =
      match cin with
      | WrapTerm i -> "Term@"^string_of_int i
      | WrapAck i -> "Ack@"^string_of_int i
      | WrapLab (i,l) -> "Lab@"^string_of_int i^": "^string_of_label l
      | WrapCh (i,n) -> "Ch@"^string_of_int i^": "^string_of_int n
      | WrapVal (i,v) -> "Val@"^string_of_int i^": "^string_of_value v

  (* We need a local map from channel ID's to action channels. Specifically,
     We need to pull messages off remote channels and then route them to the
     correct local logical channel. Since the Squeues are synchronized internally,
     we should only need lock when extending the map.
     We have one map per remote channel. *)
  let cenvSplit (cenv: channel CM.t) : (channel IM.t * int CM.t) = 
    let (x,y,_) = CM.fold cenv ~init:(IM.empty,CM.empty,0)
       ~f:(fun ~key:c ~data:ch (im,cm,n) -> (IM.add im n ch,CM.add cm c n,n+1))
    in (x,y)

  (* Mutliplexers take some initial map and then update it as it goes along.
     In an attempt to avoid over serialization, we use one lock per multiplexer. *)
  let multiplexer (cl : channel IM.t) (ic:in_channel) (oc:out_channel) : unit =
    let cl' = ref cl
    and clLock = Mutex.create ()
    in
    let freshAdd ch = let rec go n : int = if IM.mem !cl' n
                                           then go (n+1)
                                           else (cl' := IM.add !cl' n ch;
                                                n)
                      in crit clLock (fun () -> go 0)
    and lockAdd n ch = crit clLock (fun () -> cl' := IM.add !cl' n ch)
    in
    let rec gooq (i:int) ((Chan (oq,_)) as ch : channel) : unit = 
      let m' = match Catqueue.pop oq with
               | Term -> WrapTerm i
               | Ack ->  WrapAck i
               | Val v -> WrapVal (i,v)
               | Lab l -> WrapLab (i,l)
               | Ch c -> let n = freshAdd c
                         in ignore (Thread.create (gooq n) c);
                            WrapCh (i,n)
      in realOut oc bin_writer_commWrapper m';
         gooq i ch
    and goiq () = let w = try realIn ic bin_reader_commWrapper
                          with _ -> (* Exceptions hopefully mean intended termination,
                                       This means we don't get termination messages? *)
                                   Thread.exit ();
                                   abort "unreachable"
                  in let i,m = match w with
                               | WrapTerm i -> i, Term
                               | WrapAck i -> i, Ack
                               | WrapVal (i,v) -> i, Val v
                               | WrapLab (i,l) -> i, Lab l
                               | WrapCh (i,n) ->
                                 let (iq,oq) = (Catqueue.create (),Catqueue.create ())
                                 in lockAdd n (Chan (iq,oq));
                                    let _ = Thread.create (gooq n) (Chan (iq,oq)) in
                                    i, Ch (Chan (oq,iq))
                     in let Chan (_,iq) = IM.find_exn !cl' i
                        in Catqueue.push iq m;
                           goiq ()
    in ignore (Thread.create goiq ());
       IM.iter cl ~f:(fun ~key:i ~data:ch -> ignore (Thread.create (gooq i) ch))

  let unsanitieze_chans (cm:int CM.t) : channel CM.t =
    let (cenv,im) = CM.fold cm ~init:(CM.empty,IM.empty)
        ~f:(fun ~key:c ~data:i (cacc,iacc) ->
           let q1,q2 = (Catqueue.create (),Catqueue.create ())
           in (CM.add cacc c (Chan (q1,q2)),IM.add iacc i (Chan (q2,q1))))
    in multiplexer im stdin stdout;
       cenv

  let init _ = ()
  let poll _ = failwith "ssh-poll"
  let spawnRemote (env:value SM.t) (senv:shrsrc CM.t) (cenv:channel CM.t) (p:Syntax.Core.proc) (c:cvar) 
                  (state:proc_local) =
    let rec pcs = Unix.open_process_full "./sshstub.byte" (Unix.environment ())
    and errorRep ec = match In_channel.input_line ec with
                      | Some s -> crit errorLock (fun () -> prerr_endline s); errorRep ec
                      | None -> (* pretty sure this only happens when the other end ends
                                   with an exception *)
                                prerr_endline "Nothing"; failwith "Nothing"
    in let _ = Thread.create errorRep pcs.Unix.Process_channels.stderr in
       let oc,ic = pcs.Unix.Process_channels.stdin, pcs.Unix.Process_channels.stdout
       and Chan (q1,q2) as ch = Chan (Catqueue.create (),Catqueue.create ())
       in let (im,cm) = cenvSplit (CM.add cenv c ch)
          in realOut oc bin_writer_bool !eval_trace_flag;
             realOut oc bin_writer_string !backend_choice;
             realOut oc (SM.bin_writer_t bin_writer_int) !Types.Dest.conArities;
             realOut oc (List.bin_writer_t bin_writer_int) (!ancestors@[post procNum]);
             realOut oc (SM.bin_writer_t bin_writer_value) env;
             realOut oc (CM.bin_writer_t bin_writer_shrsrc) senv;
             realOut oc (CM.bin_writer_t bin_writer_int) cm;
             realOut oc Syntax.Core.bin_writer_proc p;
             multiplexer im ic oc;
             Chan (q2,q1)
  let newChan () = failwith "BUG ssh doesn't support newChan"
  let spawn (env:value SM.t) (senv:shrsrc CM.t) (cenv:channel CM.t) (p:Syntax.Core.proc) (c:cvar)
            (state:proc_local) = 
    let Chan (q1,q2) as ch : channel = Chan (Catqueue.create (),Catqueue.create ())
    in let _ = Thread.create (fun () -> SSH_Eval.eval_proc env senv (CM.add cenv c ch) p) () in
       Chan (q2,q1)
  let forward (Chan (iq1,oq1)) (Chan (iq2,oq2)) =
      Catqueue.concat iq1 oq2;
      Catqueue.concat iq2 oq1;
      Thread.exit ()
  let mkTerm () = Term
  let is_Term t = t = Term
  let write_comm (Chan (iq,oq)) comm =
    Catqueue.push oq comm;
    match Catqueue.pop iq with
    | Ack -> ()
    | _ -> failwith "got non-Ack in write_comm"
  let read_comm (Chan (iq,oq)) =
    let r = Catqueue.pop iq
    in Catqueue.push oq Ack;
       r
  let valComm v = Val v
  let getVal c = match c with Val v -> Some v | _ -> None
  let chanComm c = Ch c
  let getChan c = match c with Ch c -> Some c | _ -> None
  let boxedChanComm _ = failwith "ssh-boxedChanComm"
  let getBoxedChan _ = failwith "ssh-getBoxedChan"
  let labComm l = Lab l
  let getLab c = match c with Lab l -> Some l | _ -> None
  let procExit () = Thread.exit ()

  let globalControl : channel Squeue.t SM.t ref = ref SM.empty
  let controlLock : Mutex.t = Mutex.create ()
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
and SSH_Eval : (Evaluator with type channel = Impl_SSH.channel) = MkEvaluator(Impl_SSH)
