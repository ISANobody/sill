open Base
open Types.Dest
open Unify
open Core.Std

(* TODO check that affine isn't treated as a subtype of linear *)

(* Exceptions for various errors that can prevent subtyping *)
exception NonUniqS of stype * stype
exception GeneralSubtyping of string

let subtype_trace (s : string) : unit = if !subtype_trace_flag then print_endline ("\n"^s)

(* Decide the subtyping relation *)
(* Since we can't track our recursive assumptions implicitly by pointers here,
   we pass to lists of assumptions: one for mtypes and one for stypes *)
let rec subtypeS_raw (sass : (stype*stype) list)
  (tin1: stype) (tin2 : stype) : unit =
  subtype_trace ("subtypeS " ^string_of_stype tin1 ^" <<< "^string_of_stype tin2);
  let t1,t2 = getSType tin1, getSType tin2
  in if physeq t1 t2 || pairmemq (t1,t2) sass
     then subtype_trace ("subtypeS TERMINATO: "^string_of_stype t1^" <<< "^string_of_stype t2)
     else match !t1,!t2 with
          | SInd _,_ -> failwith "subtypeS: SInd after getSType"
          | _,SInd _ -> failwith "subtypeS: SInd after getSType"
          | Stop (_,mode1) ,Stop (_,mode2) when mode1 = mode2 -> ()
          | SVarU (_,x),SVarU (_,y) -> if not (x = y) then raise (GeneralSubtyping "Mismatched session variables")
          | SVar,_ -> if uniqSubS [] [] t2 then unifyS t1 t2 else raise (NonUniqS (t1,t2))
          | _,SVar -> if uniqSupS [] [] t1 then unifyS t1 t2 else raise (NonUniqS (t1,t2))
          | InD(_,mode1,m1,s1),InD(_,mode2,m2,s2) when mode1 = mode2 -> 
            unifyM m1 m2;
            subtypeS_raw ((t1,t2)::sass) s1 s2 
          | OutD(_,mode1,m1,s1),OutD(_,mode2,m2,s2) when mode1 = mode2 -> 
            unifyM m1 m2; 
            subtypeS_raw ((t1,t2)::sass) s1 s2 
          | InC(_,mode1,si1,sc1),InC(_,mode2,si2,sc2) when mode1 = mode2 -> 
                   subtypeS_raw ((t1,t2)::sass) si1 si2 ;
                   subtypeS_raw ((t1,t2)::sass) sc1 sc2 
          | OutC(_,mode1,si1,sc1),OutC(_,mode2,si2,sc2) when mode1 = mode2 -> 
                   subtypeS_raw ((t1,t2)::sass) si2 si1 ;
                   subtypeS_raw ((t1,t2)::sass) sc1 sc2 
          | Intern (_,mode1,c1), Intern (_,mode2,c2) when mode1 = mode2 ->
            lmIter2 c1 c2
                     (fun ~key:k ~data:d -> 
                     match d with
                     | `Both (s1,s2) -> subtypeS_raw ((t1,t2)::sass) s1 s2 
                     | `Left _ -> raise (GeneralSubtyping 
                          ("when solving "^string_of_stype t1^" <<< "^string_of_stype t2
                           ^" found label "^string_of_label k^" only on the left"))
                     | `Right _ -> ())
          | Extern (_,mode1,c1), Extern (_,mode2,c2) when mode1 = mode2 ->
            lmIter2 c1 c2
                     (fun ~key:k ~data:d -> 
                     match d with
                     | `Both (s1,s2) -> subtypeS_raw ((t1,t2)::sass) s1 s2 
                     | `Right _ -> raise (GeneralSubtyping 
                          ("when solving "^string_of_stype t1^" <<< "^string_of_stype t2
                           ^" found label "^string_of_label k^" only on the right"))
                     | `Left _ -> ())
          | Forall(_,mode1,x1,s1),Forall(_,mode2,x2,s2) when mode1 = mode2 
                                                      && x1 = x2 -> subtypeS_raw ((t1,t2)::sass) s1 s2
          | Exists(_,mode1,x1,s1),Exists(_,mode2,x2,s2) when mode1 = mode2
                                                      && x1 = x2 -> subtypeS_raw ((t1,t2)::sass) s1 s2
          | ShftUp(_,mode1,s1),ShftUp(_,mode2,s2) when mode1 = mode2 -> subtypeS_raw ((t1,t2)::sass) s1 s2
          | ShftDw(_,mode1,s1),ShftDw(_,mode2,s2) when mode1 = mode2 -> subtypeS_raw ((t1,t2)::sass) s1 s2
          | _,_ -> raise (GeneralSubtyping ("Can't solve "^string_of_stype t1^" <<< "^string_of_stype t2))
(* Calculate whether these have unique sub/supertypes. Assumptions are to deal with
   circularity *)
(* TODO acutally explain this *)
and uniqSubS (asmpSubS : stype list) (asmpSupS : stype list)
             (tin: stype) : bool = 
  let t = getSType tin in
  if memq t asmpSubS 
  then true
  else match !t with
       | SInd _ -> failwith "uniqSubS SInd after getSType"
       | SComp _ -> failwith "uniqSubS SComp after getSType"
       | Stop _ -> true
       | SVar -> false
       | SVarU _ -> true
       | Extern _ -> false
       | Intern _ -> false
       | InD (_,_,m1,s1) -> uniqSubS (t::asmpSubS) asmpSupS s1
       | OutD (_,_,m1,s1) -> uniqSubS (t::asmpSubS) asmpSupS s1
       | InC (_,_,s1,s2) -> uniqSupS ([s1;s2]@asmpSubS) asmpSupS s1
                         && uniqSubS ([s1;s2]@asmpSubS) asmpSupS s2
       | OutC (_,_,s1,s2) -> uniqSubS ([s1;s2]@asmpSubS) asmpSupS s1
                          && uniqSubS ([s1;s2]@asmpSubS) asmpSupS s2
       | Forall (_,_,_,t1) -> uniqSubS (t::asmpSubS) asmpSupS t1
       | Exists (_,_,_,t1) -> uniqSubS (t::asmpSubS) asmpSupS t1
       | ShftUp (_,_,s) -> uniqSupS (t::asmpSubS) asmpSupS s
       | ShftDw (_,_,s) -> uniqSupS (t::asmpSubS) asmpSupS s
and uniqSupS (asmpSubS : stype list) (asmpSupS : stype list)
             (tin: stype) : bool =
  let t = getSType tin in
  if memq t asmpSupS 
  then true
  else match !t with
       | SInd _ -> failwith "uniqSupS SInd after getSType"
       | SComp _ -> failwith "uniqSupS SComp after getSType"
       | Stop _ -> true
       | SVar -> false
       | SVarU _ -> true
       | Extern _ -> false
       | Intern _ -> false
       | InD (_,_,m1,s1) -> uniqSupS asmpSubS (t::asmpSupS) s1
       | OutD (_,_,m1,s1) -> uniqSupS asmpSubS (t::asmpSupS) s1
       | InC (_,_,s1,s2) -> uniqSubS asmpSubS ([s1;s2]@asmpSupS) s1
                         && uniqSupS asmpSubS ([s1;s2]@asmpSupS) s2
       | OutC (_,_,s1,s2) -> uniqSupS asmpSubS ([s1;s2]@asmpSupS) s1
                          && uniqSupS asmpSubS ([s1;s2]@asmpSupS) s2
       | Forall(_,_,_,s) -> uniqSubS asmpSubS (t::asmpSupS) s
       | Exists(_,_,_,s) -> uniqSubS asmpSubS (t::asmpSupS) s
       | ShftUp(_,_,s) -> uniqSubS asmpSubS (t::asmpSupS) s
       | ShftDw(_,_,s) -> uniqSubS asmpSubS (t::asmpSupS) s

let subtypeS t1 t2 mode = subtypeS_raw [] t1 t2; 
   subtype_trace ("subtypeSResult: "^string_of_stype t1^" <<< "^
                                    string_of_stype t2)
