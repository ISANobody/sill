open Base
open Core.Std
open Vars

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
  | InTy of srcloc * tyvar * cvar * proc
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
          | TYVar  of srcloc * tyvar
          | Int of srcloc * int
          | Paren  of ambig
          | List of ambig (* lists like [...] *)
          | Times of ambig * ambig 
          | Loli  of ambig * ambig
          | Pair of ambig * ambig
          | At of ambig
          | Arrow of ambig * ambig
 and mtype = Comp of string * mtype list
           | MonT of stype option * stype list
           | MVar  of string
 and stype = TyInD  of modality * mtype * stype
           | TyOutD of modality * mtype * stype
           | TyInC  of modality * stype * stype
           | TyOutC of modality * stype * stype
           | Stop of modality
           | Intern of modality * stype LM.t
           | Extern of modality * stype LM.t
           | Mu of tyvar * stype * string * [`A of ambig | `M of mtype | `S of stype] list (* Second two record data for printing *)
           | SVar of srcloc * tyvar (* Session type variables *)
           | SComp of srcloc * string * [`A of ambig | `M of mtype | `S of stype] list
           | Forall of modality * tyvar * stype
           | Exists of modality * tyvar * stype
           | ShftUp of modality * stype (* Only need the target modality explicit *)
           | ShftDw of modality * stype (* Only need the target modality explicit *) 
           | Parens of stype (* This is pretty ugly :/ *)
           | TyAt of stype
           | Prime of stype
           | Bang of stype
and ptype = Poly of [`M of string | `S of tyvar] list * mtype (* first one is mtype
quantifier, second session *)
with sexp, bin_io 

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
  | TYVar _ -> "TYVar"

(* Some printing functions *)
let rec string_of_mtype (tin:mtype) : string =
  match tin with
  | MVar x -> x
  | Comp (c,args) -> if List.length args = 0
                     then c
                     else c^"("^intercal string_of_mtype "," args^")"
  | MonT (Some s,ss) -> let go sx = string_of_stype sx
                        in if List.length ss = 0 
                           then "{"^go s^"}"
                           else "{"^go s ^ " <- " ^intercal go " " ss^"}"
  | MonT (None,ss) ->   let go sx = string_of_stype sx
                        in if List.length ss = 0 
                           then "{ }"
                           else "{ <- " ^intercal go " " ss^"}"
(* TODO Check this printing *)
and string_of_stype (tin : stype) : string =
  match tin with
  | TyInD (_,m,s) -> string_of_mtype m ^"=>"^string_of_stype s
  | TyOutD (_,m,s) -> string_of_mtype m ^"/\\"^string_of_stype s
  | TyInC (m1,s1,s2) -> modetag m1 ^ string_of_stype s1 ^"-o"^string_of_stype s2
  | TyOutC (m1,s1,s2) -> modetag m1 ^ string_of_stype s1 ^"*"^string_of_stype s2
  | Stop _ -> "1"
  | Intern (_,c) -> 
    "+{"^intercal (fun (l,s) -> string_of_label l^": "^string_of_stype s) "; " (LM.to_alist c)^"}"
  | Extern (_,c) ->
    "&{"^intercal (fun (l,s) -> string_of_label l^": "^string_of_stype s) "; " (LM.to_alist c)^"}"
  | SComp (_,c,args) -> if List.length args = 0
                      then c
                      else c^"("^intercal (fun x -> match x with
                                                    | `A a -> ambig2str a
                                                    | `M m -> string_of_mtype m
                                                    | `S s -> string_of_stype s)
                                           "," args^")"
  | Mu (x,s,_,_) -> "mu $"^string_of_tyvar x^". "^string_of_stype s
  | SVar (_,(_,x)) -> "$"^x
  | Forall (_,x,s) -> "forall "^string_of_tyvar x^"."^string_of_stype s
  | Exists (_,x,s) -> "exists "^string_of_tyvar x^"."^string_of_stype s
  | Parens s -> "("^string_of_stype s^")"
  | ShftUp _ -> failwith "string_of_stype ShftUp"
  | ShftDw _ -> failwith "string_of_stype ShftDw"
  | TyAt s -> "@"^string_of_stype s
  | Bang s -> "!"^string_of_stype s
  | Prime s -> "'"^string_of_stype s

(* Global map to record the mode of declared session types *)
let declModes : modality SM.t ref = ref SM.empty

(* Calculate the mode of a given type *)
let rec getmode (tin:stype) : modality =
  match tin with
  | TyInD (m,_,_) -> m
  | TyOutD (m,_,_) -> m
  | TyInC (m,_,_) -> m
  | TyOutC (m,_,_) -> m
  | Stop m -> m
  | Intern (m,_) -> m
  | Extern (m,_) -> m
  | Mu((m,_),_,_,_) -> m
  | SVar (_,(m,_)) -> m
  | SComp (l,c,_) -> if SM.mem !declModes c
                     then SM.find_exn !declModes c
                     else errr l ("Undefined session type "^c)
  | Parens s -> getmode s
  | Forall (m,_,_) -> m
  | Exists (m,_,_) -> m
  | ShftUp (m,_) -> m
  | ShftDw (m,_) -> m
  | Bang _ -> Intuist
  | TyAt _ -> Affine
  | Prime _ -> Linear

let checkStop n = if snd n = 1 
                  then Stop Linear 
                  else errr (fst n) ("Expected the session type 1 found "^string_of_int (snd n))

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
  | TYVar (l,_) -> l

let rec ambigstype (ain: ambig) : stype =
  match ain with
  | Seqq (Tyname (sloc,n)::l) -> SComp (sloc,n,List.map l (fun a -> `A (Seqq [a])))
  | Seqq [Int (sloc,n)] -> checkStop (sloc,n)
  | Times (a1,a2) -> TyOutC(Linear,ambigstype a1,ambigstype a2) (* TODO Modes *)
  | Seqq [Paren a] -> ambigstype a
  | At (Times (a1,a2)) -> TyOutC(Affine,ambigstype a1,ambigstype a2)
  | At Seqq [Int (sloc,n)] -> TyAt (checkStop (sloc,n))
  | Seqq [TYVar (l,x)] -> SVar (l,x)
  | _ -> errr (ambigl ain) "Expected a session type here"

and ambigmtype (ain: ambig) : mtype = 
  match ain with
  | Seqq (Tyname (_,n)::l) -> Comp (n,List.map l (fun a -> ambigmtype (Seqq [a])))
  | Seqq [Funname (_,n)] -> MVar n
  | Seqq [Unit _] -> Comp ("()",[])
  | Seqq [MAtom m] -> m
  | Seqq [Paren a] -> ambigmtype a
  | Seqq [List a] -> Comp ("[]",[ambigmtype a])
  | Seqq [Pair (a1,a2)] -> Comp (",",[ambigmtype a1;ambigmtype a2])
  | Arrow (a1,a2) -> Comp ("->",[ambigmtype a1; ambigmtype a2])
  | _ -> errr (ambigl ain) "Expected a data-level type here"

and ambigconst (ain: ambig) : string * mtype list = 
  (* print_endline ("ambigconst: "^ambig2str ain); *)
  match ain with
  | Seqq (Tyname (_,n)::l) -> (n,List.map l (fun a -> ambigmtype (Seqq [a])))
  | Arrow _ -> failwith "Constructors must start with an uppercase identifier"
  | _ -> failwith ("BUG ambigconst match failure: "^ambig2str ain)

let rec ambigexp (ain: ambig) : exp =
  match ain with
  | Seqq [] -> failwith "BUG: ambigexp (Seq [])"
  | Seqq (h::t) -> List.fold_left ~f:(fun acc a -> App(locE acc,acc,ambigexp a)) ~init:(ambigexp h) t
  | Unit sloc -> Sat (sloc,"()",[])
  | Tyname (sloc,x) -> Var (sloc,(sloc,x))
  | Funname (sloc,x) -> Var (sloc,(sloc,x))
  | EAtom e -> e
  | MAtom _ -> failwith "Type where expression expected"
  | Paren a -> ambigexp a
  | Int (sloc,n) -> Con(sloc,Int n)
  | Times (a1,a2) -> Bin((ambigl a1),Mul,ambigexp a1,ambigexp a2)
  | List a -> Sat(ambigl ain,"::",[ambigexp a;Sat(ambigl a,"[]",[])])
  | Pair (a1,a2) -> Sat(ambigl ain,",",[ambigexp a1;ambigexp a2])
  | _ -> failwith ("ambigexp match failure "^ambig2str ain)
(* TODO check that these are well formed? *)

(* Free variables *)
(* TODO Better name *)
let rec freeMVarsMPure (tin:mtype) : SS.t =
  match tin with
  | MVar x -> SS.singleton x
  | Comp (_,args) -> List.fold_left args 
                                        ~init:SS.empty
                                        ~f:(fun s a -> SS.union s (freeMVarsMPure a))
  | MonT (Some s,ss) -> SS.union (freeMVarsSPure s)
                                     (List.fold_left ss
                                        ~init:SS.empty
                                        ~f:(fun acc a -> SS.union acc (freeMVarsSPure a)))
  | MonT (None,ss) -> (List.fold_left ss
                                      ~init:SS.empty
                                      ~f:(fun acc a -> SS.union acc (freeMVarsSPure a)))
(* TODO this name has the module name in it.... *)
and freeMVarsSPure (tin:stype) : SS.t =
  match tin with
  | TyInD (_,m,s) -> SS.union (freeMVarsMPure m) (freeMVarsSPure s)
  | TyOutD (_,m,s) -> SS.union (freeMVarsMPure m) (freeMVarsSPure s)
  | TyInC (_,s1,s2) -> SS.union (freeMVarsSPure s1) (freeMVarsSPure s2)
  | TyOutC (_,s1,s2) -> SS.union (freeMVarsSPure s1) (freeMVarsSPure s2)
  | Stop _ -> SS.empty
  | Intern (_,c) -> LM.fold c ~init:SS.empty 
                                ~f:(fun ~key:_ ~data:s a -> SS.union a (freeMVarsSPure s))
  | Extern (_,c) -> LM.fold c ~init:SS.empty
                                 ~f:(fun ~key:_ ~data:s a -> SS.union a (freeMVarsSPure s))
  | Mu (_,s,_,_) -> freeMVarsSPure s
  | SVar _ -> SS.empty
  | SComp (l,name,args) ->
    (match SM.find !sessionQs name with
    | Some qs ->
      if not (List.length qs = List.length args)
      then errr l ("Number of arguments, "^string_of_int (List.length args)
                  ^", to "^name^" doesn't match its expectation of "
                  ^string_of_int (List.length qs));
      List.fold2_exn qs args 
           ~init:SS.empty
           ~f:(fun s q a -> match q,a with
                        | `M _,`M x -> SS.union s (freeMVarsMPure x)
                        | `M _,`A x -> SS.union s (freeMVarsMPure (ambigmtype x))
                        | `S _,`A x -> SS.union s (freeMVarsSPure (ambigstype x))
                        | `S _,`S x -> SS.union s (freeMVarsSPure x)
                        | _ -> failwith "BUG freeMVarsSPure.1")
    | None -> errr l ("Undefined session type "^name))
  | Forall (_,_,s) -> freeMVarsSPure s
  | Exists (_,_,s) -> freeMVarsSPure s
  | Parens s -> freeMVarsSPure s
  | ShftUp (_,s) -> freeMVarsSPure s
  | ShftDw (_,s) -> freeMVarsSPure s
  | Bang s -> freeMVarsSPure s
  | TyAt s -> freeMVarsSPure s
  | Prime s -> freeMVarsSPure s

let rec freeSVarsMPure (tin:mtype) : TS.t =
  match tin with
  | MVar _ -> TS.empty
  | Comp (_,args) -> List.fold_left args
                                    ~init:TS.empty
                                    ~f:(fun m a -> TS.union m (freeSVarsMPure a))
  | MonT (Some s,ss) -> TS.union (freeSVarsSPure s)
                                     (List.fold_left ss
                                        ~init:TS.empty
                                        ~f:(fun acc a -> TS.union acc (freeSVarsSPure a)))
  | MonT (None,ss) -> (List.fold_left ss
                                      ~init:TS.empty
                                      ~f:(fun acc a -> TS.union acc (freeSVarsSPure a)))
(* TODO decide if overloading type variables by modality is ok *)
(* TODO Move freevariable stuff to be closer together *)
and freeSVarsSPure (tin:stype) : TS.t =
  match tin with
  | TyInD (_,m,s) -> TS.union (freeSVarsMPure m) (freeSVarsSPure s)
  | TyOutD (_,m,s) -> TS.union (freeSVarsMPure m) (freeSVarsSPure s)
  | TyInC (_,s1,s2) -> TS.union (freeSVarsSPure s1) (freeSVarsSPure s2)
  | TyOutC (_,s1,s2) -> TS.union (freeSVarsSPure s1) (freeSVarsSPure s2)
  | Stop _ -> TS.empty
  | Intern (_,c) -> LM.fold c ~init:TS.empty 
                              ~f:(fun ~key:_ ~data:s a -> TS.union a (freeSVarsSPure s))
  | Extern (_,c) -> LM.fold c ~init:TS.empty
                              ~f:(fun ~key:_ ~data:s a -> TS.union a (freeSVarsSPure s))
  | Mu (x,s,_,_) -> TS.remove (freeSVarsSPure s) x
  | SVar (_,x) -> TS.singleton x
  | SComp (_,_,args) -> List.fold_left args 
                                     ~init:TS.empty
                                     ~f:(fun s a -> match a with
                                                    | `A _ -> TS.empty (* TODO fix this *)
                                                    | `M x -> TS.union s (freeSVarsMPure x)
                                                    | `S x -> TS.union s (freeSVarsSPure x))
  | Forall (_,x,s) -> TS.remove (freeSVarsSPure s) x
  | Exists (_,x,s) -> TS.remove (freeSVarsSPure s) x
  | Parens s -> freeSVarsSPure s
  | ShftUp (_,s) -> freeSVarsSPure s
  | ShftDw (_,s) -> freeSVarsSPure s
  | Bang s -> freeSVarsSPure s
  | TyAt s -> freeSVarsSPure s
  | Prime s -> freeSVarsSPure s

type toplet =
  | TopExp of fvar * (fvar*[`M of mtype | `P of ptype]) * fvar list * exp
  | TopMon of fvar * (fvar*[`M of mtype | `P of ptype]) * fvar list * cvar * proc * cvar list
  | TopDet of fvar * (fvar*[`M of mtype | `P of ptype]) * fvar list * srcloc * proc * cvar list

type toplvl =
  | TopLets of toplet FM.t
  | TopProc of (cvar * proc) list
  | MTypeDecl of fvar * fvar list * mtype list SM.t (* C a = C a b c *)
  | STypeDecl of modality * fvar * [`M of string | `S of tyvar] list * stype (* C a = s *)
  | ServDecl of fvar * stype

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


