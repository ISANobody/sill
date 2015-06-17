open Base
open Core.Std
open Vars

(* The purpose of this is to allow for parsing and desugaring to occur at different times.
   It is assumed that you'll use the fully qualified names with this. *)
(* TODO consider just making these applications of _building_or_ or something *)
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
   | Sat of srcloc * string * exp list (* TODO make constructors just a variable lookup *)
   | If of srcloc * exp * exp * exp
   | Case of srcloc * exp * ((fvar list * exp) SM.t)
   | Fun of srcloc * fvar * fvar list * exp
   | App of srcloc * exp * exp
   | Let of srcloc * [`M of mtype | `P of ptype] * fvar * fvar list * exp * exp
   | Monad of srcloc * cvar option * proc * cvar list
   | Cast of srcloc * exp * mtype
   | Box of srcloc * exp * mtype
   | PolyApp of srcloc * fvar * stype list (* x<S> *)
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
  | SendSync of srcloc * cvar * proc (* send c shift; P *)
  | RecvSync of srcloc * cvar * proc (* shift <- recv c; P *)
 and tyapp = TyApp of fvar * [`A of fvar | `M of mtype | `S of stype] list
 and mtype = Comp of srcloc * string * [`A of fvar | `M of mtype | `S of stype] list
           | MonT of srcloc * stype option * stype list
           | MVar  of srcloc * string
 and stype = TyInD  of srcloc * modality * mtype * stype
           | TyOutD of srcloc * modality * mtype * stype
           | TyInC  of srcloc * modality * stype * stype
           | TyOutC of srcloc * modality * stype * stype
           | Stop of srcloc * modality
           | Intern of srcloc * modality * stype LM.t
           | Extern of srcloc * modality * stype LM.t
           | Mu of srcloc * tyvar * stype * string * [`A of fvar | `M of mtype | `S of stype] list (* Second two record data for printing *)
           | SVar of srcloc * tyvar (* Session type variables *)
           | SComp of srcloc * string * [`A of fvar | `M of mtype | `S of stype] list
           | Forall of srcloc * modality * tyvar * stype
           | Exists of srcloc * modality * tyvar * stype
           | ShftUp of srcloc * modality * stype (* Only need the target modality explicit *)
           | ShftDw of srcloc * modality * stype (* Only need the target modality explicit *) 
           | TyAt of srcloc * stype (* TODO is this ugly name needed? *)
           | Prime of srcloc * stype
           | Bang of srcloc * stype
           | Sync of srcloc * stype
and ptype = Poly of string list * tyvar list * mtype (* first one is mtype
quantifier, second session *)
with sexp, bin_io 

let tyapp2mtype (TyApp (name,args)) : mtype = Comp (fst name,snd name,args)

(* TODO Disambiguate more intelligently *)
let tyapp2stype (TyApp (name,args)) : stype = SComp (fst name,snd name,args)

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

let rec locS : stype -> srcloc = function
  | ShftDw (i,_,_) -> i
  | TyInD (i,_,_,_) -> i
  | TyOutD (i,_,_,_) -> i
  | TyInC (i,_,_,_) -> i
  | TyOutC (i,_,_,_) -> i
  | Stop (i,_) -> i
  | Intern (i,_,_) -> i
  | Extern (i,_,_) -> i
  | Mu (i,_,_,_,_) -> i
  | SVar (i,_) -> i
  | SComp (i,_,_) -> i
  | Forall (i,_,_,_) -> i
  | Exists (i,_,_,_) -> i
  | ShftUp (i,_,_) -> i
  | TyAt (i,_) -> i
  | Prime (i,_) -> i
  | Bang (i,_) -> i
  | Sync (i,_) -> i

(* Global map to record the mode of declared session types *)
let declModes : modality SM.t ref = ref SM.empty
let declPoles : [`Pos | `Neg] SM.t ref = ref SM.empty

(* Calculate the mode of a given type *)
let rec getmode (tin:stype) : modality =
  match tin with
  | TyInD (_,m,_,_) -> m
  | TyOutD (_,m,_,_) -> m
  | TyInC (_,m,_,_) -> m
  | TyOutC (_,m,_,_) -> m
  | Stop (_,m) -> m
  | Intern (_,m,_) -> m
  | Extern (_,m,_) -> m
  | Mu(_,(m,_),_,_,_) -> m
  | SVar (_,(m,_)) -> m
  | SComp (l,c,_) -> if SM.mem !declModes c
                       then SM.find_exn !declModes c
                       else errr l ("Undefined session type "^c)
  | Forall (_,m,_,_) -> m
  | Exists (_,m,_,_) -> m
  | ShftUp (_,m,_) -> m
  | ShftDw (_,m,_) -> m
  | Bang (_,_) -> Intuist
  | TyAt (_,_) -> Affine
  | Prime (_,_) -> Linear
  | Sync (_,s) -> getmode s

(* TODO Confirm that these 'BUG's cannot arise *)
(* This might be more cleanly reflected by splitting stype into stype_neg and stype_pos *)
let rec polarity : stype -> [`Pos | `Neg] = function
  | TyInD _ -> `Neg
  | TyOutD _ -> `Pos
  | TyInC _ -> `Neg
  | TyOutC _ -> `Pos
  | Stop _ -> `Pos
  | Intern _ -> `Pos
  | Extern _ -> `Neg
  | (Mu _ as t) -> failwith ("Fullsyntax.polarity BUG Mu of "^string_of_stype t)
  | SVar _ -> `Pos
  | SComp (l,n,_) -> (match SM.find !declPoles n with
                   | Some p -> p 
                   | None -> errr l ("Unknown session type "^n))
  | Forall _ -> `Neg
  | Exists _ -> `Pos
  | ShftUp _ -> `Neg
  | ShftDw _ -> `Pos
  | Bang (_,s) when getmode s < Intuist -> `Neg
  | Bang (l,s) ->  polarity (Sync (l,s))
  | TyAt (_,s) when getmode s > Affine -> `Pos
  | TyAt (_,s) when getmode s < Affine -> `Neg
  | TyAt (l,s) -> polarity (Sync (l,s))
  | Prime (_,s) when getmode s > Linear -> `Pos
  | Prime (l,s) -> polarity (Sync (l,s))
  | Sync (_,s) -> (match polarity s with `Pos -> `Neg | `Neg -> `Pos)

(* Some printing functions *)
and string_of_mtype (tin:mtype) : string =
  match tin with
  | MVar (_,x) -> x
  | Comp (_,"[]",[`M a]) -> "["^string_of_mtype a^"]"
  | Comp (_,",",[`M a;`M b]) -> "("^string_of_mtype a^", "^string_of_mtype b^")"
  | Comp (_,"->",[`M a;`M b]) -> "("^string_of_mtype a^") -> ("^string_of_mtype b^")"
  | Comp (_,c,args) -> if List.length args = 0
                     then c
                     else c^"("^intercal (function
                                         | `A a -> snd a
                                         | `M m -> string_of_mtype m
                                         | `S s -> string_of_stype s) "," args^")"
  | MonT (_,Some s,ss) -> let go sx = string_of_stype sx
                        in if List.length ss = 0 
                           then "{"^go s^"}"
                           else "{"^go s ^ " <- " ^intercal go " " ss^"}"
  | MonT (_,None,ss) ->   let go sx = string_of_stype sx
                        in if List.length ss = 0 
                           then "{ }"
                           else "{ <- " ^intercal go " " ss^"}"
(* TODO Check this printing *)
and string_of_stype (tin : stype) : string =
  match tin with
  | TyInD (_,_,m,s) -> string_of_mtype m ^"=>"^string_of_stype s
  | TyOutD (_,_,m,s) -> string_of_mtype m ^"/\\"^string_of_stype s
  | TyInC (_,m1,s1,s2) -> modetag m1 ^ string_of_stype s1 ^"-o"^string_of_stype s2
  | TyOutC (_,m1,s1,s2) -> modetag m1 ^ string_of_stype s1 ^"*"^string_of_stype s2
  | Stop _ -> "1"
  | Intern (_,_,c) -> 
    "+{"^intercal (fun (l,s) -> string_of_label l^": "^string_of_stype s) "; " (LM.to_alist c)^"}"
  | Extern (_,_,c) ->
    "&{"^intercal (fun (l,s) -> string_of_label l^": "^string_of_stype s) "; " (LM.to_alist c)^"}"
  | SComp (_,c,args) -> if List.length args = 0
                      then c
                      else c^"("^intercal (fun x -> match x with
                                                    | `A a -> string_of_fvar a
                                                    | `M m -> string_of_mtype m
                                                    | `S s -> string_of_stype s)
                                           "," args^")"
  | Mu (_,x,s,_,_) -> "mu $"^string_of_tyvar x^". "^string_of_stype s
  | SVar (_,x) -> string_of_tyvar x
  | Forall (_,_,x,s) -> "forall "^string_of_tyvar x^"."^string_of_stype s
  | Exists (_,_,x,s) -> "exists "^string_of_tyvar x^"."^string_of_stype s
  | ShftUp _ -> failwith "string_of_stype ShftUp"
  | ShftDw _ -> failwith "string_of_stype ShftDw"
  | TyAt (_,s) -> "@"^string_of_stype s
  | Bang (_,s) -> "!"^string_of_stype s
  | Prime (_,s) -> "'"^string_of_stype s
  | Sync (_,s) -> modetag (getmode s)^string_of_stype s

(* Free variables *)
(* TODO Better name *)
let rec freeMVarsMPure (tin:mtype) : SS.t =
  match tin with
  | MVar (_,x) -> SS.singleton x
  | Comp (_,_,args) -> List.fold_left args 
                                        ~init:SS.empty
                                        ~f:(fun s -> (function
                                                     | `A _ -> s
                                                     | `M a -> SS.union s (freeMVarsMPure a)
                                                     | `S a -> SS.union s (freeMVarsSPure a)))
  | MonT (_,Some s,ss) -> SS.union (freeMVarsSPure s)
                                     (List.fold_left ss
                                        ~init:SS.empty
                                        ~f:(fun acc a -> SS.union acc (freeMVarsSPure a)))
  | MonT (_,None,ss) -> (List.fold_left ss
                                      ~init:SS.empty
                                      ~f:(fun acc a -> SS.union acc (freeMVarsSPure a)))
(* TODO this name has the module name in it.... *)
and freeMVarsSPure (tin:stype) : SS.t =
  match tin with
  | TyInD (_,_,m,s) -> SS.union (freeMVarsMPure m) (freeMVarsSPure s)
  | TyOutD (_,_,m,s) -> SS.union (freeMVarsMPure m) (freeMVarsSPure s)
  | TyInC (_,_,s1,s2) -> SS.union (freeMVarsSPure s1) (freeMVarsSPure s2)
  | TyOutC (_,_,s1,s2) -> SS.union (freeMVarsSPure s1) (freeMVarsSPure s2)
  | Stop (_,_) -> SS.empty
  | Intern (_,_,c) -> LM.fold c ~init:SS.empty 
                                ~f:(fun ~key:_ ~data:s a -> SS.union a (freeMVarsSPure s))
  | Extern (_,_,c) -> LM.fold c ~init:SS.empty
                                 ~f:(fun ~key:_ ~data:s a -> SS.union a (freeMVarsSPure s))
  | Mu (_,_,s,_,_) -> freeMVarsSPure s
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
                        |  _  ,`A _ -> SS.empty (* Types with no arguments can't have free vars *)
                        | `S _,`S x -> SS.union s (freeMVarsSPure x)
                        | _ -> failwith "BUG freeMVarsSPure.1")
    | None -> errr l ("Undefined session type "^name))
  | Forall (_,_,_,s) -> freeMVarsSPure s
  | Exists (_,_,_,s) -> freeMVarsSPure s
  | ShftUp (_,_,s) -> freeMVarsSPure s
  | ShftDw (_,_,s) -> freeMVarsSPure s
  | Bang (_,s) -> freeMVarsSPure s
  | TyAt (_,s) -> freeMVarsSPure s
  | Prime (_,s) -> freeMVarsSPure s
  | Sync (_,s) -> freeMVarsSPure s

let rec freeSVarsMPure (tin:mtype) : TS.t =
  match tin with
  | MVar _ -> TS.empty
  | Comp (_,_,args) -> List.fold_left args
                                    ~init:TS.empty
                                    ~f:(fun m -> function
                                                 | `A _ -> TS.empty
                                                 | `M a -> TS.union m (freeSVarsMPure a)
                                                 | `S a -> TS.union m (freeSVarsSPure a))
  | MonT (_,Some s,ss) -> TS.union (freeSVarsSPure s)
                                     (List.fold_left ss
                                        ~init:TS.empty
                                        ~f:(fun acc a -> TS.union acc (freeSVarsSPure a)))
  | MonT (_,None,ss) -> (List.fold_left ss
                                      ~init:TS.empty
                                      ~f:(fun acc a -> TS.union acc (freeSVarsSPure a)))
(* TODO decide if overloading type variables by modality is ok *)
(* TODO Move freevariable stuff to be closer together *)
and freeSVarsSPure (tin:stype) : TS.t =
  match tin with
  | TyInD (_,_,m,s) -> TS.union (freeSVarsMPure m) (freeSVarsSPure s)
  | TyOutD (_,_,m,s) -> TS.union (freeSVarsMPure m) (freeSVarsSPure s)
  | TyInC (_,_,s1,s2) -> TS.union (freeSVarsSPure s1) (freeSVarsSPure s2)
  | TyOutC (_,_,s1,s2) -> TS.union (freeSVarsSPure s1) (freeSVarsSPure s2)
  | Stop _ -> TS.empty
  | Intern (_,_,c) -> LM.fold c ~init:TS.empty 
                              ~f:(fun ~key:_ ~data:s a -> TS.union a (freeSVarsSPure s))
  | Extern (_,_,c) -> LM.fold c ~init:TS.empty
                              ~f:(fun ~key:_ ~data:s a -> TS.union a (freeSVarsSPure s))
  | Mu (_,x,s,_,_) -> TS.remove (freeSVarsSPure s) x
  | SVar (_,x) -> TS.singleton x
  | SComp (_,_,args) -> List.fold_left args 
                                     ~init:TS.empty
                                     ~f:(fun s a -> match a with
                                                    | `A _ -> TS.empty (* TODO fix this *)
                                                    | `M x -> TS.union s (freeSVarsMPure x)
                                                    | `S x -> TS.union s (freeSVarsSPure x))
  | Forall (_,_,x,s) -> TS.remove (freeSVarsSPure s) x
  | Exists (_,_,x,s) -> TS.remove (freeSVarsSPure s) x
  | ShftUp (_,_,s) -> freeSVarsSPure s
  | ShftDw (_,_,s) -> freeSVarsSPure s
  | Bang (_,s) -> freeSVarsSPure s
  | TyAt (_,s) -> freeSVarsSPure s
  | Prime (_,s) -> freeSVarsSPure s
  | Sync (_,s) -> freeSVarsSPure s

type toplet = (* TODO Should be a record? *)
  | TopExp of fvar  (* name *)
            * [`M of mtype | `P of ptype] (* Fully qualified type or not? *)
            * tyvar list option (* Session Quantifier list *)
            * fvar list (* argument names *)
            * exp (* Body of definition *)
  | TopMon of fvar (* name *)
            * [`M of mtype | `P of ptype] (* Fully quantified type? *)
            * tyvar list option (* Session Quantifier list *)
            * fvar list  (* functional arguments *)
            * cvar  (* Provided channel *)
            * proc  (* process  body *)
            * cvar list (* channel arguments *)
  | TopDet of fvar (* Name *)
            * [`M of mtype | `P of ptype] (* Fully quantified type? *)
            * tyvar list option (* Session Quantiifer list *)
            * fvar list (* functional arguments *)
            * srcloc  (* src location of the binding (can't pull it from a variable name) *)
            * proc  (* process body *)
            * cvar list (* channel arguments *)

type toplvl =
  | TopLets of (fvar * ptype * fvar list * exp)
  | TopLets_ of toplet
  | TopProc of (cvar * proc) list
  | MTypeDecl of fvar * [`M of string | `S of tyvar] list * mtype list SM.t (* C a = C a b c *)
  | STypeDecl of modality * fvar * [`M of string | `S of tyvar] list * stype (* C a = s *)
  | ServDecl of fvar * stype (* TODO Is this still used? *)

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
  | SendSync (i,_,_) -> i
  | RecvSync (i,_,_) -> i

let locToplet (tin:toplet) : srcloc =
  match tin with
  | TopExp (name,_,_,_,_) -> fst name
  | TopMon (name,_,_,_,_,_,_) -> fst name
  | TopDet (name,_,_,_,_,_,_) -> fst name

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
  | SendSync (_,c,p) -> CS.add (freeCVars p) c
  | RecvSync (_,c,p) -> CS.add (freeCVars p) c


