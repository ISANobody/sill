open Base
open Syntax.Core
open Types.Dest

(* It's unfortunate that we have two nearly identical unification functions,
   but I don't know how to write a more generic one without a lot of casting *)

(* These could do with more information *)
exception Infinite of string
exception MismatchedM of string

let iter2 (m1:'a SM.t) (m2:'a SM.t)
          (f:string -> [ `Both of 'v1 * 'v2 | `Left of 'v1 | `Right of 'v2 ] -> unit) : unit =
  let _ = SM.merge m1 m2 (fun ~key:k d -> f k d; None) in ()

let subtypemap : (stype * stype) list ref = ref []
let subcache (tin1 : stype) (tin2 : stype) : bool = 
   let b = List.exists  (fun (x,y) -> x == tin1 && y == tin2) !subtypemap
   in subtypemap := (tin1,tin2)::!subtypemap;
      b
  
let rec unifyM_raw (tin1 : mtype) (tin2 : mtype) (mode:[`Both | `LeftOnly | `RightOnly | `Neither]) : unit =
  if !unify_trace_flag
       then print_endline ("UnifyM: " ^ string_of_mtype tin1 ^ " === " ^ string_of_mtype tin2^"\n");
  let t1,t2 = getMType tin1, getMType tin2
  in if t1 == t2
     then ()
     else match !t1,!t2 with
          | MInd _,_ -> failwith "unifyM: MInd after getMType"
          | _,MInd _ -> failwith "unifyM: MInd after getMType"
          | MVar,_ -> (match mode with
                      | `Both | `LeftOnly -> if  List.memq t1 (freeMVars t2)
                      then raise (Infinite "left var")
                      else t1 := MInd t2
                      | `RightOnly | `Neither -> failwith "Unify left var")
          | _,MVar -> (match mode with
                      | `Both | `RightOnly -> (if List.memq t2 (freeMVars t1)
                                 then raise (Infinite "right var")
                                 else t2 := MInd t1)
                      | `LeftOnly | `Neither -> failwith "Unify right var")
          | MVarU x1, MVarU x2 when x1 = x2 -> ()
          | Comp(c1,as1),Comp(c2,as2) ->
            if not (c1 = c2 && List.length as1 = List.length as2) then raise (MismatchedM "Comp");
            t1 := MInd t2; (* TODO iter2 here? *)
            List.fold_left2 (fun () a1 a2 -> 
              match a1,a2 with
              | `M x,`M y -> unifyM_raw x y mode
              | `S x,`S y -> unifyS_raw x y mode
              | _ -> raise (MismatchedM "Comp")) () as1 as2
          | MonT(Some s1,sm1),MonT(Some s2,sm2) ->
            if not (List.length sm1 = List.length sm2)
            then failwith ("Can't unify "^string_of_mtype t1^" and "^string_of_mtype t2
                          ^" mismatch argument number");
            t1 := MInd t2;
            unifyS_raw s1 s2 mode;
            List.iter2 (fun a b -> unifyS_raw a b mode) sm1 sm2
          | _ -> raise (MismatchedM ("UnifyM: etc "^string_of_mtype t1
                                           ^" =/= "^string_of_mtype t2))

and unifyS_raw (tin1 : stype) (tin2 : stype) (mode:[`Both | `LeftOnly | `RightOnly | `Neither]) : unit =
  if !unify_trace_flag
       then print_endline ("UnifyS: " ^ string_of_stype tin1 ^ " === " ^ string_of_stype tin2^"\n");
  let t1,t2 = getSType tin1, getSType tin2
  in if t1 == t2
     then ()
     else match !t1,!t2 with
          | SInd _,_ -> failwith "unifyS: SInd after getSType"
          | _,SInd _ -> failwith "unifyS: SInd after getSType"
          | SVar,_ -> (match mode with
                      | `Both | `LeftOnly -> t1 := SInd t2;
                      | `RightOnly | `Neither -> failwith "SVar Left during `RightOnly/`Neither")
          | _,SVar -> (match mode with
                      | `Both | `RightOnly -> t2 := SInd t1;
                      | `LeftOnly | `Neither -> failwith "SVar Left during `LeftOnly/`Neither")
            (* TODO confirm that mode mismatches give reasonable error messages *)
          | SVarU x1,SVarU x2 when x1 = x2 -> ()
          | Stop mode1,Stop mode2 when mode1 = mode2 -> t1 := SInd t2
          | InD(mode1,m1,s1),InD(mode2,m2,s2) when mode1 = mode2 -> 
            t1 := SInd t2; 
            unifyM_raw m1 m2 mode; 
            unifyS_raw s1 s2 mode
          | OutD(mode1,m1,s1),OutD(mode2,m2,s2) when mode1 = mode2 -> 
            t1 := SInd t2; 
            unifyM_raw m1 m2 mode; 
            unifyS_raw s1 s2 mode
          | OutC (mode1,a1,b1),OutC (mode2,a2,b2) when mode1 = mode2 
               -> t1 := SInd t2; unifyS_raw a1 a2 mode; unifyS_raw b1 b2 mode
          | InC (mode1,a1,b1),InC (mode2,a2,b2) when mode1 = mode2 
               -> t1 := SInd t2; unifyS_raw a1 a2 mode; unifyS_raw b1 b2 mode
          | Extern (mode1,c1), Extern (mode2,c2) when mode1 = mode2 -> 
            t1 := SInd t2;
            lmIter2 c1 c2 
                     (fun ~key:k ~data:d -> match d with
                          | `Both (s1,s2) -> unifyS_raw s1 s2 mode
                          | `Left _ -> failwith ("unifyS: found key "^string_of_label k^" only on the left")
                          | `Right _ -> failwith ("unifyS: found key "^string_of_label k^" only on the right"))
          | Intern (mode1,c1), Intern (mode2,c2) when mode1 = mode2 -> 
            t1 := SInd t2;
            lmIter2 c1 c2 
                     (fun ~key:k ~data:d -> match d with
                          | `Both (s1,s2) -> unifyS_raw s1 s2 mode
                          | `Left _ -> failwith ("unifyS: found key "^string_of_label k^" only on the left")
                          | `Right _ -> failwith ("unifyS: found key "^string_of_label k^" only on the right"))
          (* TODO alpha convert *)
          | Forall(mode1,x1,s1),Forall(mode2,x2,s2) when mode1 = mode2 && x1 = x2 ->
            t1 := SInd t2;
            unifyS_raw s1 s2 mode
          (* TODO alpha convert *)
          | Exists(mode1,x1,s1),Exists(mode2,x2,s2) when mode1 = mode2 && x1 = x2 ->
            t1 := SInd t2;
            unifyS_raw s1 s2 mode
          | ShftUp(mode1,s1),ShftUp(mode2,s2) when mode1 = mode2 ->
            t1 := SInd t2;
            unifyS_raw s1 s2 mode
          | ShftDw(mode1,s1),ShftDw(mode2,s2) when mode1 = mode2 ->
            t1 := SInd t2;
            unifyS_raw s1 s2 mode
          | _ -> failwith ("can't unify: "^string_of_stype t1^" and "^string_of_stype t2)

let unifyM t1 t2 = unifyM_raw t1 t2 `Both
let unifyS t1 t2 = unifyS_raw t1 t2 `Both

(* Matches t1 against t2, i.e., "finds" s s.t., s(t1)=t2 *)
(* Works by disabling the rule for t === x *)
let matchM (tin1 : mtype) (tin2 : mtype) : unit = unifyM_raw tin1 tin2 `RightOnly
