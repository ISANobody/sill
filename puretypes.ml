open Base
open Core.Std

type mtype = Comp of string * mtype list
           | MonT of stype option * stype list
           | Var  of string
 and stype = InD  of modality * mtype * stype
           | OutD of modality * mtype * stype
           | InC  of modality * stype * stype
           | OutC of modality * stype * stype
           | Stop of modality
           | Intern of modality * stype LM.t
           | Extern of modality * stype LM.t
           | Mu of tyvar * stype * string * mtype list (* Second two record data for printing *)
           | SVar of srcloc * tyvar (* Session type variables *)
           | SComp of srcloc * string * mtype list
           | Forall of modality * tyvar * stype
           | Exists of modality * tyvar * stype
           | ShftUp of modality * stype (* Only need the target modality explicit *)
           | ShftDw of modality * stype (* Only need the target modality explicit *) 
           | Parens of stype (* This is pretty ugly :/ *)
           | At of stype
           | Prime of stype
           | Bang of stype
 with sexp, bin_io
type ptype = Poly of [`M of string | `S of tyvar] list * mtype with sexp, bin_io (* first one is mtype
quantifier, second session *)

(* Some printing functions *)
let rec string_of_mtype (tin:mtype) : string =
  match tin with
  | Var x -> x
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
  | InD (_,m,s) -> string_of_mtype m ^"=>"^string_of_stype s
  | OutD (_,m,s) -> string_of_mtype m ^"/\\"^string_of_stype s
  | InC (m1,s1,s2) -> modetag m1 ^ string_of_stype s1 ^"-o"^string_of_stype s2
  | OutC (m1,s1,s2) -> modetag m1 ^ string_of_stype s1 ^"*"^string_of_stype s2
  | Stop _ -> "1"
  | Intern (_,c) -> 
    "+{"^intercal (fun (l,s) -> string_of_label l^": "^string_of_stype s) "; " (LM.to_alist c)^"}"
  | Extern (_,c) ->
    "&{"^intercal (fun (l,s) -> string_of_label l^": "^string_of_stype s) "; " (LM.to_alist c)^"}"
  | SComp (_,c,args) -> if List.length args = 0
                      then c
                      else c^"("^intercal string_of_mtype "," args^")"
  | Mu (x,s,_,_) -> "mu $"^string_of_tyvar x^". "^string_of_stype s
  | SVar (_,(_,x)) -> "$"^x
  | Forall (_,x,s) -> "forall "^string_of_tyvar x^"."^string_of_stype s
  | Exists (_,x,s) -> "exists "^string_of_tyvar x^"."^string_of_stype s
  | Parens s -> "("^string_of_stype s^")"
  | ShftUp _ -> failwith "string_of_stype ShftUp"
  | ShftDw _ -> failwith "string_of_stype ShftDw"
  | At s -> "@"^string_of_stype s
  | Bang s -> "!"^string_of_stype s
  | Prime s -> "'"^string_of_stype s

(* Global map to record the mode of declared session types *)
let declModes : modality SM.t ref = ref SM.empty

(* Calculate the mode of a given type *)
let rec getmode (tin:stype) : modality =
  match tin with
  | InD (m,_,_) -> m
  | OutD (m,_,_) -> m
  | InC (m,_,_) -> m
  | OutC (m,_,_) -> m
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
  | At _ -> Affine
  | Prime _ -> Linear

(* TODO check that these are well formed? *)

(* Free variables *)
(* TODO Better name *)
let rec freeMVarsMPure (tin:mtype) : SS.t =
  match tin with
  | Var x -> SS.singleton x
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
  | InD (_,m,s) -> SS.union (freeMVarsMPure m) (freeMVarsSPure s)
  | OutD (_,m,s) -> SS.union (freeMVarsMPure m) (freeMVarsSPure s)
  | InC (_,s1,s2) -> SS.union (freeMVarsSPure s1) (freeMVarsSPure s2)
  | OutC (_,s1,s2) -> SS.union (freeMVarsSPure s1) (freeMVarsSPure s2)
  | Stop _ -> SS.empty
  | Intern (_,c) -> LM.fold c ~init:SS.empty 
                                ~f:(fun ~key:_ ~data:s a -> SS.union a (freeMVarsSPure s))
  | Extern (_,c) -> LM.fold c ~init:SS.empty
                                 ~f:(fun ~key:_ ~data:s a -> SS.union a (freeMVarsSPure s))
  | Mu (_,s,_,_) -> freeMVarsSPure s
  | SVar _ -> SS.empty
  | SComp (_,_,args) -> List.fold_left args 
                                     ~init:SS.empty
                                     ~f:(fun s a -> SS.union s (freeMVarsMPure a))
  | Forall (_,_,s) -> freeMVarsSPure s
  | Exists (_,_,s) -> freeMVarsSPure s
  | Parens s -> freeMVarsSPure s
  | ShftUp (_,s) -> freeMVarsSPure s
  | ShftDw (_,s) -> freeMVarsSPure s
  | Bang s -> freeMVarsSPure s
  | At s -> freeMVarsSPure s
  | Prime s -> freeMVarsSPure s

let rec freeSVarsMPure (tin:mtype) : TS.t =
  match tin with
  | Var _ -> TS.empty
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
  | InD (_,m,s) -> TS.union (freeSVarsMPure m) (freeSVarsSPure s)
  | OutD (_,m,s) -> TS.union (freeSVarsMPure m) (freeSVarsSPure s)
  | InC (_,s1,s2) -> TS.union (freeSVarsSPure s1) (freeSVarsSPure s2)
  | OutC (_,s1,s2) -> TS.union (freeSVarsSPure s1) (freeSVarsSPure s2)
  | Stop _ -> TS.empty
  | Intern (_,c) -> LM.fold c ~init:TS.empty 
                              ~f:(fun ~key:_ ~data:s a -> TS.union a (freeSVarsSPure s))
  | Extern (_,c) -> LM.fold c ~init:TS.empty
                              ~f:(fun ~key:_ ~data:s a -> TS.union a (freeSVarsSPure s))
  | Mu (x,s,_,_) -> TS.remove (freeSVarsSPure s) x
  | SVar (_,x) -> TS.singleton x
  | SComp (_,_,args) -> List.fold_left args 
                                     ~init:TS.empty
                                     ~f:(fun s a -> TS.union s (freeSVarsMPure a))
  | Forall (_,x,s) -> TS.remove (freeSVarsSPure s) x
  | Exists (_,x,s) -> TS.remove (freeSVarsSPure s) x
  | Parens s -> freeSVarsSPure s
  | ShftUp (_,s) -> freeSVarsSPure s
  | ShftDw (_,s) -> freeSVarsSPure s
  | Bang s -> freeSVarsSPure s
  | At s -> freeSVarsSPure s
  | Prime s -> freeSVarsSPure s
