(* Circularity strikes again *)
open Base
open Core.Std
open Puretypes
open Fullsyntax

let checkStop n = if snd n = 1 then Stop Linear else errr (fst n) "Expected 1 found something else"

let rec ambigstype (ain: ambig) : stype =
  match ain with
  | Seqq (Tyname (sloc,n)::l) -> SComp (sloc,n,List.map l (fun a -> ambigmtype (Seqq [a])))
  | Seqq [Int (sloc,n)] -> checkStop (sloc,n)
  | Times (a1,a2) -> Puretypes.OutC(Linear,ambigstype a1,ambigstype a2) (* TODO Modes *)
  | Seqq [Paren a] -> ambigstype a
  | At (Times (a1,a2)) -> Puretypes.OutC(Affine,ambigstype a1,ambigstype a2)
  | At Seqq [Int (sloc,n)] -> At (checkStop (sloc,n))
  | _ -> errr (ambigl ain) "Expected a session type here"

and ambigmtype (ain: ambig) : mtype = 
  match ain with
  | Seqq (Tyname (_,n)::l) -> Comp (n,List.map l (fun a -> ambigmtype (Seqq [a])))
  | Seqq [Funname (_,n)] -> Puretypes.Var n
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
