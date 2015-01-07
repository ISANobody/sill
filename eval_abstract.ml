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
  val init : unit -> unit
  val log : string -> unit
  val print : string -> unit
  val spawn : (value SM.t) -> (shrsrc CM.t) -> (channel CM.t) -> proc -> cvar -> channel
  val spawnRemote : (value SM.t) -> (shrsrc CM.t) -> (channel CM.t) -> proc -> cvar -> channel
  val newChan : unit -> channel * channel
  val free : channel -> unit
  val read_comm : channel -> communicable
  val write_comm : channel -> communicable -> unit
  val is_Term : communicable -> bool
  val mkTerm : unit -> communicable
  val valComm : value -> communicable
  val getVal : communicable -> value option 
  val chanComm : channel -> communicable
  val getChan : communicable -> channel option 
  val boxedChanComm : Puretypes.stype -> channel -> communicable
  val getBoxedChan : communicable -> (Puretypes.stype * channel) option
  val labComm : label -> communicable
  val getLab : communicable -> label option
  val forward : channel -> channel -> unit
  val procExit : unit -> unit
  val request : string -> channel
  val register : string -> channel -> unit
  val abort : string -> 'a
  val print : string -> unit
end
