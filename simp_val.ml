open Base
open Core.Std
open Syntax.Core
open Vars

(* To prevent circularity when compiling this needs to be in a separate file. *)
type simpVal = IntVal of int 
                | FloatVal of float
                | StringVal of string
                | ADT of string * simpVal list
                | Cypher of string
                | Recvar of string * exp * simpVal SM.t
                | Closure of string * exp * simpVal SM.t
                | MonV of cvar * cvar list * proc * simpVal SM.t
                | Boxed of Puretypes.mtype * simpVal
                | BoxedS of Puretypes.stype * simpShr
                | Shared of simpShr
and simpShr = ShrSrc of cvar * proc * simpVal SM.t * (simpShr CM.t)
with sexp, bin_io
