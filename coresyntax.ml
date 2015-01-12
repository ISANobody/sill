open Base
open Core.Std
open Vars

type astinfo = { linenum : int; (* These first two should probably just be a srcloc *)
                 charnum : int; 
                 affineFrees : CS.t ref (* Represent free instructions inserted right
                                           before this one. Since we don't actually
                                           perform transformations, this is easier. *) } 
with sexp, bin_io

(* Should these be in syntax.ml? *)
let ast2loc (a : astinfo) : srcloc =
    {lnum = a.linenum; cnum = a.charnum}

let nullloc = { lnum = 0; cnum = 0}
let nullinfo = { linenum = 0; charnum = 0; affineFrees = ref CS.empty }

(* constants for PicoML *)
type const = Int of int | Float of float | String of string with sexp, bin_io

let string_of_const c =
    match c 
    with Int n    -> string_of_int n
       | Float f  -> Float.to_string f
       | String s -> "\"" ^ s ^ "\""

(* Infixed binary operators for PicoML *)
type binop = Add | Sub | Mul | Div | Exp | FAdd | FSub | FMul | FDiv 
           | Concat | Eq | Less
with sexp, bin_io

let string_of_binop = function 
     Add  -> " + "
   | Sub -> " - "
   | Mul -> " * "
   | Div -> " / "
   | Exp -> " ** "
   | FAdd -> " +. "
   | FSub -> " -. "
   | FMul -> " *. "
   | FDiv -> " /. "
   | Concat -> " ^ "
   | Eq  -> " = "
   | Less -> " < "

(* Primitive unary operator in PicoML *)
type monop = Print | Neg | Assert | PrintStr | Flush | IToS | SexpToS | Sleep with sexp, bin_io

let string_of_monop m =
    match m with
       | Neg   -> "~"
       | Assert -> "assert"
       | PrintStr -> "print_str"
       | Print -> "print"
       | Flush -> "flush"
       | IToS -> "i2s"
       | SexpToS -> "sexp2s"
       | Sleep -> "sleep"


(* ASTInfo is not included in the descriptions *)
type exp =  
   | Var of astinfo * fvar                (* variables *)
   | Con of astinfo * const                 (* constants *)
   | Sat of astinfo * string * exp list     (* saturated constructor *)
   | App of astinfo * exp * exp             (* exp1 exp2 *)
   | Bin of astinfo * binop * exp * exp     (* exp1 % exp2
                                        where % is a builtin binary operator *)
   | Mon of astinfo * monop * exp           (* % exp1
                                        where % is a builtin monadic operator *)
   | Fun of astinfo * fvar * exp          (* fun x -> exp *)
   | Let of astinfo * [`M of Fullsyntax.mtype | `P of Fullsyntax.ptype] * fvar * exp * exp    (* let x = exp1 in exp2 *)
   | Cas of astinfo * exp * ((fvar list * exp) SM.t)
   | Monad of astinfo * cvar option * proc * cvar list * procType option (* c <-{P}<- cs *)
   | Cast of astinfo * exp * Fullsyntax.mtype (* <e:t> *)
   | Box of astinfo * exp * Fullsyntax.mtype (* [e:t] *)
   | PolyApp of astinfo * fvar * [`A of Fullsyntax.ambig | `S of Fullsyntax.stype] list (* x<S,S,...> *)
and proc =
   | Bind of astinfo * cvar * exp * cvar list * proc (* c <- e -< cs; P *)
   | TailBind of astinfo * cvar * exp * cvar list (* c <- e -< cs *)
   | Service of astinfo * cvar * fvar * proc (* c <- service Foo; P *)
   | Register of astinfo * fvar * cvar * proc (* register Foo c; P *)
   | InputD of astinfo * fvar * cvar * proc          (* x <- input c; P *)
   | OutputD of astinfo * cvar * exp * proc            (* output c e; P *)
   | InputC of astinfo * [`Tensor | `DwCastL | `UpCastR ] ref * cvar * cvar * proc          (* c <- input d; P *)
   | OutputC of astinfo * cvar * cvar * proc * proc  (* output c (d <- P); Q *)
   | Close of astinfo * cvar                           (* close c *)
   | Exit of astinfo 
   | Wait of astinfo * cvar * proc                     (* wait c; P *)
   | External of astinfo * cvar * proc LM.t            (* case c of SM *)
   | Internal of astinfo * cvar * label * proc        (* select c.l; P *)
   | Fwd of astinfo * cvar * cvar                   (* fwd c d *)
   | InputTy of astinfo * tyvar * cvar * proc
   | OutputTy of astinfo * cvar * Fullsyntax.stype * proc
   | ShftUpL of astinfo * cvar * cvar * proc (* c1 <- send c2; P *)
   | ShftDwR of astinfo * cvar * cvar * proc (* send c1 (c2 <- P) *)

(* Type for holding information need for our dynamic type checks.
   In particular, every monadic value has a set of quantifiers, a map from expressions to
   types, and a map from proc expressions to types. We use the maps to get the dynamic
   type we either need to check or add as a tag. The set of quantifiers then is used at
   run time to instantiate these local checks with new monomorphic variables that can be
   safely unified against without destroying our overall types. An alternate approach
   might have stored the checking information closer to its use, but I think this would
   require walking the entire AST and duplicating most of it, which could be much more
   expensive if there is a large amount of non-dynamically checked functional code. *)
and procType = ProcType of SS.t * (proc * Fullsyntax.mtype) list * (proc * Fullsyntax.stype) list
with sexp, bin_io (* TODO Do we use procType? *)

type toplvl = TopLet of (fvar * [`M of Fullsyntax.mtype | `P of Fullsyntax.ptype] * exp) (* let f : tau = ... ;; *)
            | TopProc of cvar * proc
            | MTypeDecl of fvar * fvar list * Fullsyntax.mtype list SM.t
            | STypeDecl of fvar * [`M of string | `S of tyvar] list * Fullsyntax.stype
            | Pass
            | ServDecl of fvar * Fullsyntax.stype

let getinfoE (e:exp) : astinfo = 
  match e with
  | Var (i,_) -> i
  | Con (i,_) -> i
  | Sat (i,_,_) -> i
  | App (i,_,_) -> i
  | Bin (i,_,_,_) -> i
  | Mon (i,_,_) -> i
  | Fun (i,_,_) -> i
  | Let (i,_,_,_,_) -> i
  | Cas (i,_,_) -> i
  | Monad (i,_,_,_,_) -> i
  | Cast (i,_,_) -> i
  | Box (i,_,_) -> i
  | PolyApp (i,_,_) -> i
let getinfoP (p:proc) : astinfo =
  match p with
  | TailBind (i,_,_,_) -> i
  | Bind (i,_,_,_,_) -> i
  | InputD (i,_,_,_) -> i
  | OutputD (i,_,_,_) -> i
  | InputC (i,_,_,_,_) -> i
  | OutputC (i,_,_,_,_) -> i
  | Close (i,_) -> i
  | Exit i -> i
  | Wait (i,_,_) -> i
  | External (i,_,_) -> i
  | Internal (i,_,_,_) -> i
  | Fwd (i,_,_) -> i
  | OutputTy (i,_,_,_) -> i
  | InputTy (i,_,_,_) -> i
  | Service (i,_,_,_) -> i
  | Register (i,_,_,_) -> i
  | ShftUpL (i,_,_,_) -> i
  | ShftDwR (i,_,_,_) -> i
  
let locE (e:exp) : srcloc = ast2loc (getinfoE e)
let locP (p:proc) : srcloc = ast2loc (getinfoP p)
