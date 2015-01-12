open Base
open Core.Std
open Syntax.Core
open Vars
open Sexplib

type memory = value SM.t
and value =
  | Intval of int
  | Floatval of float
  | Stringval of string                
  | Closure of string * exp * memory
  | Recvar of string * exp * memory
  | ADT of string * value list
  | MonV of cvar option * cvar list * proc * memory
  | Cypher of string
  | Boxed of Fullsyntax.mtype * value
  | BoxedS of Fullsyntax.stype * value
  | Shared of shrsrc
and shrsrc = ShrSrc of cvar * proc * memory * (shrsrc CM.t)
with sexp, bin_io

(*value output*)
let rec string_of_value v =
   match v with
  | Intval n          -> string_of_int n 
  | Floatval r        -> Float.to_string r
  | Stringval s       -> ("\"" ^ s ^ "\"")
  | Closure _ -> "<closure>"
  | Recvar _  -> "<recvar>"
  | MonV _ -> "<Monad>"
  | ADT ("$RSA.pub",_) -> "<RSA public key>"
  | ADT ("$RSA.priv",_) -> "<RSA private key>"
  | ADT (x,l) -> x^"(" ^ (let rec pl = function
                          | []     -> ")"
                          | v::[]  -> string_of_value v ^ ")"
                          | v::vs  -> string_of_value v ^ "; " ^ pl vs
                          in pl l)
  | Cypher _ -> "<Cypher>"
  | Boxed (t,v) -> "<"^string_of_value v^":"^Fullsyntax.string_of_mtype t^">"
  | Shared (ShrSrc (_,p,_,_)) -> "<Replicable Service "^(loc2str (locP p))^">"
  | BoxedS (t,Shared ((ShrSrc (_,p,_,_)))) -> "<Replicable Service "^(loc2str (locP p))
                                             ^"::"^Fullsyntax.string_of_stype t^">"
  | BoxedS _ -> failwith "value.ml: string_of_value: non-Shared in BoxedS"

let unbox v =
  match v with
  | Boxed (_,v') -> v'
  | _ -> v

