open Base
open Core.Std
open Vars
open Value
open Syntax.Core

(* To prevent circularity when compiling this needs to be in a separate file. *)



module type Impl =
sig
  type channel
  type communicable
  type proc_local = { id : int list; (* Address in the ancestor relation tree *)
                      childCounter : int ref; (* Number of children spawned so far *)
                      (* What was the last channel we used and in what polarity *)
                      focusCache : [`Send of channel | `Recv of channel] option ref;
                      (* How many times did we communicate along the same channel/polarity *)
                      focusCounter : int ref;
                      unfocusCounter : int ref;
                    }
  val init : unit -> unit
  val log : int list -> string -> unit
  val print : string -> unit
  val spawn : (value SM.t) -> (shrsrc CM.t) -> (channel CM.t) -> proc -> cvar -> proc_local -> channel
  val spawnRemote : (value SM.t) -> (shrsrc CM.t) -> (channel CM.t) -> proc -> cvar -> proc_local -> channel
  val newChan : unit -> channel * channel
  val free : channel -> unit
  val read_comm : proc_local -> channel -> communicable
  val write_comm : proc_local -> channel -> communicable -> unit
  val is_Term : communicable -> bool
  val mkTerm : unit -> communicable
  val valComm : value -> communicable
  val getVal : communicable -> value option 
  val chanComm : channel -> communicable
  val getChan : communicable -> channel option 
  val boxedChanComm : Fullsyntax.stype -> channel -> communicable
  val getBoxedChan : communicable -> (Fullsyntax.stype * channel) option
  val labComm : label -> communicable
  val getLab : communicable -> label option
  val forward : channel -> channel -> unit
  val procExit : proc_local -> unit
  val request : string -> channel
  val register : string -> channel -> unit
  val abort : string -> 'a
  val print : string -> unit
end
