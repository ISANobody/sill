open Base
open Core.Std
open Value
open Vars
open Eval_functor
open Eval_abstract

let abort (s:string) = prerr_endline s; Pervasives.exit 1

module TM = Map.Make(Int)

let threadMap : string TM.t ref = ref TM.empty
let threadLock = Mutex.create ()

module rec Impl_Thread : Impl =
struct
  type communicable = Chan of channel
                    | BoxedChan of Puretypes.stype * channel
                    | Term
                    | Val of value
                    | Lab of label
  and channel = (communicable Catqueue.t * communicable Catqueue.t) (* write * read *)
  let string_of_comm c =
      match c with
      | Chan _ -> "Chan"
      | Lab l -> "label "^string_of_label l
      | Val v -> "val "^string_of_value v
      | Term -> "Term"
      | BoxedChan _ -> "BoxedChan"
  let init () = ()
  let abort _ = failwith "async-abort unimplemented"
  let log s =
    Mutex.lock threadLock;
    print_endline (string_of_int (Thread.id (Thread.self ()))^": "^s);
    (match TM.find !threadMap (Thread.id (Thread.self ())) with
    | Some x -> threadMap := TM.add !threadMap (Thread.id (Thread.self ())) (x^"\n"^s)
    | None -> threadMap := TM.add !threadMap (Thread.id (Thread.self ())) s);
    Mutex.unlock threadLock
  let print = Mutex.synchronize (fun s -> print_string s; flush stdout)
  let procExit () = Thread.exit ()
  let free _ = failwith "free unimplemented"
  let mkTerm () = Term
  let is_Term c = match c with Term -> true | _ -> false
  let valComm v = Val v
  let getVal c = match c with Val v -> Some v | _ -> None
  let labComm l = Lab l
  let getLab c = match c with Lab l -> Some l | _ -> None
  let chanComm ch = Chan ch
  let getChan c = match c with Chan ch -> Some ch | _ -> None
  let boxedChanComm s ch = BoxedChan (s,ch)
  let getBoxedChan c = match c with BoxedChan (s,ch) -> Some (s,ch) | _ -> None
  let write_comm ch c = Catqueue.push (fst ch) c
  let rec read_comm ch = Catqueue.pop (snd ch)
  let spawn (env:value SM.t) senv (cenv:Thread_Eval.channel CM.t) (p:Syntax.Core.proc) (c:cvar) =
    let ch : Thread_Eval.channel = (Catqueue.create (),Catqueue.create ())
    in let _ = Thread.create (fun () -> Thread_Eval.eval_proc env senv (CM.add cenv c ch) p) ()
       in (snd ch,fst ch)
  let spawnRemote = spawn
  let newChan () = let (c1,c2) = (Catqueue.create (),Catqueue.create ())
                   in ((c1,c2),(c2,c1))
  let forward chin1 chin2 =
    Catqueue.concat (fst chin1) (snd chin2);
    Catqueue.concat (fst chin2) (snd chin1);
    Thread.exit ()
  let poll _ = failwith "thread_async-poll undefined"
  let request _ = failwith "thread_async-request unimplemented"
  let register _ = failwith "thread_asyn-register unimplemented"
end
and Thread_Eval : (Evaluator with type channel = (Impl_Thread.communicable Catqueue.t *
Impl_Thread.communicable Catqueue.t)) = MkEvaluator(Impl_Thread)
