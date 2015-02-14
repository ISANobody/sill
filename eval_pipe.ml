open Base
open Core.Std
open Value
open Syntax.Core
open Vars
open Eval_functor
open Eval_abstract

let tempdir = ref ""

let mktempfifo () = 
 let (name,fd) = Unix.mkstemp (!tempdir^"/fifo")
 in Unix.close fd;
    Unix.unlink name;
    Unix.mkfifo name ~perm:0o666;
    name
             
type channel_raw = 
  | BothOpen of ((string * Unix.File_descr.t) * (string * Unix.File_descr.t))
  | LeftOpen of ((string * Unix.File_descr.t) * string)
  | RightOpen of (string * (string * Unix.File_descr.t))
  | NoneOpen of (string * string)

type pipe_channel = channel_raw ref

let mkchan () : pipe_channel = ref (NoneOpen (mktempfifo (),mktempfifo ()))

let swappol ch =
  match !ch with
  | NoneOpen (s1,s2) -> ref (NoneOpen (s2,s1))
  | _ -> prerr_endline "Swap of Open channel"; Pervasives.exit 1

type pipe_comm = 
  | Ack
  | Term
  | Val of value
  | Chan of (string * string)
  | BoxedChan of (Fullsyntax.stype * string * string)
  | Lab of label
  with bin_io

let read_comm_raw (ch:pipe_channel) : pipe_comm =
  let fd = match !ch with
           | BothOpen (_,(_,c)) -> c
           | LeftOpen (x,s) -> let f = Unix.openfile ~mode:[Unix.O_RDONLY] s
                               in ch := BothOpen (x,(s,f));
                                  f
           | RightOpen (_,(_,c)) -> c
           | NoneOpen (x,s) -> let f = Unix.openfile ~mode:[Unix.O_RDONLY] s
                               in ch := RightOpen (x,(s,f));
                                  f
  in Bin_prot.Utils.bin_read_stream ~read:(fun t ~pos:p ~len:l -> Bigstring.really_read fd ~pos:p ~len:l t)
                                    bin_reader_pipe_comm

let write_comm_raw (ch:pipe_channel) (c:pipe_comm) : unit =
  let fd : Unix.File_descr.t = match !ch with
           | BothOpen ((_,f),_) -> f
           | RightOpen (s,x) -> let f = Unix.openfile ~mode:[Unix.O_WRONLY] s
                                in ch := BothOpen ((s,f),x);
                                   f
           | LeftOpen ((_,f),_) -> f
           | NoneOpen (s1,s2) -> let f = Unix.openfile ~mode:[Unix.O_WRONLY] s1
                                 in ch := LeftOpen ((s1,f),s2);
                                    f
  in Bigstring.really_write fd (Bin_prot.Utils.bin_dump ~header:true bin_writer_pipe_comm c)

let pipe_read_comm (ch:pipe_channel) : pipe_comm =
   match read_comm_raw ch with
   | Term -> Term
   | x -> write_comm_raw ch Ack;
          x

let pipe_write_comm (ch:pipe_channel) (c:pipe_comm) : unit =
  match c with
  | Term -> write_comm_raw ch Term
  | _ -> write_comm_raw ch c;
         match read_comm_raw ch with
         | Ack -> ()
         | _ -> prerr_endline "Got Non-Ack of send. BUG."; Pervasives.exit 1

let pipe_forward (chin1:pipe_channel) (chin2:pipe_channel) : unit =
  let rec go (ch1:pipe_channel) (ch2:pipe_channel) =
    let r = try read_comm_raw ch1 
            with Bigstring.IOError (_,End_of_file) -> 
            (* EOF errors are from a Term *)
            Pervasives.exit 0
    in
    match r with
    | Term -> write_comm_raw ch2 Term; Pervasives.exit 0
    | x -> write_comm_raw ch2 x;
           go ch1 ch2
  in match Unix.fork () with
     | `In_the_child -> go chin2 chin1
     | `In_the_parent _ -> go chin1 chin2

module rec Impl_Pipe : Impl =
struct
  type channel = pipe_channel
  type controlChan = ControlChan
  type communicable = pipe_comm
  type proc_local = { id : int list; (* Address in the ancestor relation tree *)
                      childCounter : int ref; (* Number of children spawned so far *)
                      (* What was the last channel we used and in what polarity *)
                      focusCache : [`Send of channel | `Recv of channel] option ref;
                      (* How many times did we communicate along the same channel/polarity *)
                      focusCounter : int ref;
                      unfocusCounter : int ref;
                    }
  let procExit _ = Pervasives.exit 0
  let abort _ = failwith "pipe-abort unimplemented"
  let init () = tempdir := Unix.mkdtemp "sill-temp"
  let log _ = failwith "pipe-log unimplemented"
  let free _ = failwith "pipe-free unimplemented"
  let print s = print_string s; flush stdout
  let is_Term c = match c with Term -> true | _ -> false
  let write_comm _ = pipe_write_comm
  let read_comm _ = pipe_read_comm
  let spawn (env: value SM.t) (senv:shrsrc CM.t) (cenv : pipe_channel CM.t) (p:proc) (c:cvar) 
            (state:Pipe_Eval.proc_local) : channel =
    let ch = mkchan()
    in match Unix.fork () with
       | `In_the_child -> (Pipe_Eval.eval_proc env senv (CM.add cenv c ch) p state; 
                          errr (fst c) "eval-proc finished? BUG")
       | `In_the_parent _ -> swappol ch
  let spawnRemote = spawn
  let newChan () = failwith "BUG eval_pipe doesn't support newChan"
  let mkTerm () = Term
  let valComm (v:value) = Val v
  let getVal (c:pipe_comm) = match c with Val v -> Some v | _ -> None
  let labComm (l:label) = Lab l
  let getLab (c:pipe_comm) = match c with Lab l -> Some l | _ -> None
  let chanComm (ch:channel) = match !ch with
                              | NoneOpen x -> Chan x
                              | _ -> abort "Tried to send open channel."
  let getChan (c:pipe_comm) = match c with Chan x -> Some (ref (NoneOpen x)) | _ -> None
  let boxedChanComm s (ch:channel) = match !ch with
                                     | NoneOpen x -> BoxedChan (s,fst x,snd x)
                                     | _ -> abort "Tried to send open channel."
  let getBoxedChan comm = match comm with
                          | BoxedChan (s,c1,c2) -> Some (s,ref (NoneOpen (c1,c2))) 
                          | _ -> None
  let forward = pipe_forward
  let poll _ = failwith "pipe-poll undefined"
  let request _ = failwith "pipe-request unimplemented"
  let register _ = failwith "pipe-register unimplemented"
end
and Pipe_Eval : (Evaluator with type channel = pipe_channel) = MkEvaluator(Impl_Pipe)
