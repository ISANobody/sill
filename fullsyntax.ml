open Base
open Core.Std
open Vars
open Puretypes

(* The purpose of this is to allow for parsing and desugaring to occur at different times.
   It is assumed that you'll use the fully qualified names with this. *)
type binop = Add | Sub | Mul | Div | Exp | FAdd | FSub | FMul | FDiv 
           | Concat | Eq | Less 
           | And | Or | GT | GE | LE
with sexp, bin_io

type const = Int of int | Float of float | String of string
with sexp, bin_io

type exp =
   | Var of srcloc * fvar
   | Con of srcloc * const
   | Bin of srcloc * binop * exp * exp
   | Sat of srcloc * string * exp list
   | If of srcloc * exp * exp * exp
   | Case of srcloc * exp * ((fvar list * exp) SM.t)
   | Fun of srcloc * fvar * fvar list * exp
   | App of srcloc * exp * exp
   | Let of srcloc * [`M of mtype | `P of ptype] * fvar * fvar list * exp * exp
   | Monad of srcloc * cvar option * proc * cvar list
   | Cast of srcloc * exp * mtype
   | Box of srcloc * exp * mtype
   | PolyApp of srcloc * fvar * [`A of ambig | `S of stype] list (* x<S> *)
and proc =
  | Bind of srcloc * cvar * exp * cvar list * proc
  | Detached of srcloc  * exp * cvar list * proc
  | TailBind of srcloc * cvar * exp * cvar list
  | Service of srcloc * cvar * fvar * proc
  | Register of srcloc * fvar * cvar * proc
  | InD of srcloc * fvar * cvar * proc
  | OutD of srcloc * cvar * exp * proc
  | InC of srcloc * cvar * cvar * proc
  | OutC of srcloc * cvar * cvar * proc * proc
  | Throw of srcloc * cvar * cvar * proc
  | Close of srcloc * cvar
  | Exit of srcloc
  | Wait of srcloc * cvar * proc
  | Fwd of srcloc * cvar * cvar
  | External of srcloc * cvar * proc LM.t
  | Internal of srcloc * cvar * label * proc
  | Abort of srcloc
  | CaseP of srcloc * exp * ((fvar list * proc) SM.t)
  | IfP of srcloc * exp * proc * proc
  | Seq of srcloc * exp * proc
  | LetP of srcloc * [`M of mtype | `P of ptype] * fvar * fvar list * exp * proc
  | InTy of srcloc * fvar * cvar * proc
  | OutTy of srcloc * cvar * stype * proc
  | ShftUpL of srcloc * cvar * cvar * proc (* c1 <- send c2; P *)
  | ShftDwR of srcloc * cvar * cvar * proc (* send c1 (c2 <- P) *)
(* While this isn't syntax exactly, circularity needs to be broken *)
and ambig = Seqq of ambig list
          | Tyname of srcloc * string
          | Funname of srcloc * string
          | Unit   of srcloc
          | MAtom  of mtype
          | EAtom  of exp
          | Int of srcloc * int
          | Paren  of ambig
          | List of ambig (* lists like [...] *)
          | Times of ambig * ambig 
          | Loli  of ambig * ambig
          | Pair of ambig * ambig
          | At of ambig
          | Arrow of ambig * ambig
with sexp, bin_io

type toplet =
  | TopExp of fvar * (fvar*[`M of mtype | `P of ptype]) * fvar list * exp
  | TopMon of fvar * (fvar*[`M of mtype | `P of ptype]) * fvar list * cvar * proc * cvar list
  | TopDet of fvar * (fvar*[`M of mtype | `P of ptype]) * fvar list * srcloc * proc * cvar list

type toplvl =
  | TopLets of toplet FM.t
  | TopProc of (cvar * proc) list
  | MTypeDecl of fvar * fvar list * mtype list SM.t (* C a = C a b c *)
  | STypeDecl of modality * fvar * fvar list * stype (* C a = s *)
  | ServDecl of fvar * stype

let locE (e:exp) : srcloc =
  match e with
  | Var (i,_) -> i
  | Con (i,_) -> i
  | Bin (i,_,_,_) -> i
  | If (i,_,_,_) -> i
  | Case (i,_,_) -> i
  | Fun (i,_,_,_) -> i
  | App (i,_,_) -> i
  | Sat (i,_,_) -> i
  | Let (i,_,_,_,_,_) -> i
  | Monad (i,_,_,_) -> i
  | Cast (i,_,_) -> i
  | Box (i,_,_) -> i
  | PolyApp (i,_,_) -> i

let locP (p:proc) : srcloc =
  match p with
  | Bind (i,_,_,_,_) -> i
  | InD (i,_,_,_) -> i
  | OutD (i,_,_,_) -> i
  | InC (i,_,_,_) -> i
  | OutC (i,_,_,_,_) -> i
  | Throw (i,_,_,_) -> i
  | Close (i,_) -> i
  | Wait (i,_,_) -> i
  | Fwd (i,_,_) -> i
  | External (i,_,_) -> i
  | Internal (i,_,_,_) -> i
  | Abort i -> i
  | TailBind (i,_,_,_) -> i
  | CaseP (i,_,_) -> i
  | IfP (i,_,_,_) -> i
  | Seq (i,_,_) -> i
  | LetP (i,_,_,_,_,_) -> i
  | Register (i,_,_,_) -> i
  | Service (i,_,_,_) -> i
  | InTy (i,_,_,_) -> i
  | OutTy (i,_,_,_) -> i
  | Detached (i,_,_,_) -> i
  | Exit i -> i
  | ShftUpL (i,_,_,_) -> i
  | ShftDwR (i,_,_,_) -> i

let locToplet (tin:toplet) : srcloc =
  match tin with
  | TopExp (name,_,_,_) -> fst name
  | TopMon (name,_,_,_,_,_) -> fst name
  | TopDet (name,_,_,_,_,_) -> fst name

let rec freeCVars (pin:proc) : CS.t =
  match pin with
  | Bind (_,c,_,cs,p) -> CS.union (CS.remove (freeCVars p) c) (CS.of_list cs)
  | InD (_,_,c,p) -> CS.add (freeCVars p) c
  | OutD (_,c,_,p) -> CS.add (freeCVars p) c
  | InC (_,cx,cc,p) -> CS.add (CS.add (freeCVars p) cx) cc
  | OutC (_,cc,ct,pt,p) -> CS.add (CS.union (freeCVars p) (CS.remove (freeCVars pt) ct)) cc
  | Throw (_,cc,ct,p) -> CS.add (CS.add (freeCVars p) cc) ct
  | Close (_,c) -> CS.singleton c
  | Wait (_,c,p) -> CS.add (freeCVars p) c
  | Fwd (_,c1,c2) -> CS.of_list [c1;c2]
  | External (_,c,br) -> CS.add (CS.union_list (LM.data (LM.map br freeCVars))) c
  | Internal (_,c,_,p) -> CS.add (freeCVars p) c
  | Abort _ -> CS.empty
  | TailBind (_,c,_,cs) -> CS.of_list cs
  | CaseP (_,_,br) -> CS.union_list (SM.data (SM.map br (fun (_,p) -> freeCVars p)))
  | IfP (_,_,pt,pf) -> CS.union (freeCVars pt) (freeCVars pf)
  | Seq (_,_,p) -> freeCVars p
  | LetP (_,_,_,_,_,p) -> freeCVars p
  | Register (_,_,c,p) -> CS.add (freeCVars p) c
  | Service (_,c,_,p) -> CS.remove (freeCVars p) c
  | OutTy (_,c,_,p) -> CS.add (freeCVars p) c
  | InTy (_,_,c,p) -> CS.add (freeCVars p) c
  | Exit _ -> CS.empty
  | Detached (_,_,cs,p) -> CS.union (freeCVars p) (CS.of_list cs)
  | ShftUpL (_,c1,c2,p) -> CS.add (CS.remove (freeCVars p) c1) c2
  | ShftDwR (_,c1,c2,p) -> CS.add (CS.remove (freeCVars p) c2) c1


let rec ambig2str (ain:ambig) : string =
  match ain with
  | Seqq l -> "Seq ["^intercal ambig2str "; " l^"]"
  | Tyname _ -> "Tyname"
  | Funname _ -> "Funname"
  | Unit _ -> "Unit"
  | MAtom _ -> "MAtom"
  | EAtom _ -> "EAtom"
  | Paren a -> "Paren "^ambig2str a
  | List a -> "List "^ambig2str a
  | Times (a1,a2) -> "Times ("^ambig2str a1^","^ambig2str a2^")"
  | Loli (a1,a2) -> "Loli ("^ambig2str a1^","^ambig2str a2^")"
  | Pair (a1,a2) -> "Pair ("^ambig2str a1^","^ambig2str a2^")"
  | Arrow (a1,a2) -> "Arrow ("^ambig2str a1^","^ambig2str a2^")"
  | Int _ -> "Int"
  | At a -> "At "^ambig2str a

let ambigcons (x:ambig) (lin:ambig) : ambig =
  match lin with
  | Seqq l -> Seqq (x::l)
  | _ -> failwith "BUG. ambigcons of non-Seq"

let ambigcat (lin1:ambig) (lin2:ambig) : ambig =
  match lin1,lin2 with
  | Seqq l1,Seqq l2 -> Seqq (l1 @ l2)
  | _ -> failwith "BUG. ambigcat of non-Seq"

let ambigsnoc (lin:ambig) (x:ambig) : ambig =
  match lin with
  | Seqq l -> Seqq (l@[x])
  | _ -> failwith "BUG. ambigsnoc of non-Seq"

let rec ambigl (ain: ambig) : srcloc =
  match ain with
  | Seqq [] -> failwith "BUG ambigl []"
  | Seqq (h::_) -> ambigl h
  | Unit sloc -> sloc
  | Tyname (sloc,_) -> sloc
  | Funname (sloc,_) -> sloc
  | EAtom e -> locE e
  | MAtom _ -> failwith "BUG ambigl MAtom"
  | Times (a,_) -> ambigl a
  | Int (sloc,_) -> sloc
  | List a -> ambigl a
  | Pair (a,_) -> ambigl a
  | Paren a -> ambigl a
  | Arrow (a,_) -> ambigl a
  | Loli (a,_) -> ambigl a
  | At a -> ambigl a
