open Base
open Core.Std
open Unify
open Types

(* This file implements the mapping from our pointer based types to the purely algebraic
ones. To do this we will maintain two mappings, one from pointer variables to names and
one from names to pointers. Maybe this should be a stack of maps to represent scoping
correctly? *)

let vartoptr_map : Dest.mtype SM.t ref = ref SM.empty
let perm_v2p_map : Dest.mtype SM.t ref = ref SM.empty
let ptrtovar_map : (Dest.mtype * string) list ref = ref []
let svartoptr_map : Dest.stype SM.t ref = ref SM.empty
let perm_s2p_map : Dest.stype SM.t ref = ref SM.empty
let ptrtosvar_map : (Dest.stype * string) list ref = ref []

let name_counter : int ref = ref 0

let vartoptr (x:string) : Dest.mtype =
  match SM.find !perm_v2p_map x with
  | Some m -> m
  | None ->
    match SM.find !vartoptr_map x with
    | Some m -> m
    | None ->
      let a = ref (Dest.MVarU x)
      in vartoptr_map := SM.add !vartoptr_map x a;
         a

let ptrtovar (min : Dest.mtype) : string = 
  let m = Dest.getMType min in 
  if ass_memq m !ptrtovar_map
  then assq m !ptrtovar_map
  else let s = "$$$"^string_of_int (post name_counter)
       in ptrtovar_map := (m,s) :: !ptrtovar_map;
          perm_v2p_map := SM.add !perm_v2p_map s m;
          s

let sptrtovar (tin : Dest.stype) : string = 
  let t = Dest.getSType tin in 
  if ass_memq t !ptrtosvar_map
  then assq t !ptrtosvar_map
  else let s = "$$$"^string_of_int (post name_counter)
       in ptrtosvar_map := (t,s) :: !ptrtosvar_map;
          perm_s2p_map := SM.add !perm_s2p_map s t;
          s

let svartoptr (x:string) : Dest.stype =
  match SM.find !perm_s2p_map x with
  | Some s -> s
  | None -> 
    match SM.find !svartoptr_map x with
    | Some s -> s
    | None -> 
      let a = ref (Dest.SVarU (Linear,x)) (* TODO modes *)
      in svartoptr_map := SM.add !svartoptr_map x a;
         a

let clearmaps (():unit) : unit = vartoptr_map := SM.empty;
                                 svartoptr_map := SM.empty

(* Essentially we're keeping track of polymorphic quantifiers without creating a
   specific type for them. This is probably bad/confusing, but session type declarations
   are treated like typedefs and are expanded at parse time, so I don't see the need to
   clutter up everything by adding SPoly (or something) to types.ml *)
let sessionDefs : ([`M of string | `S of tyvar] list * Dest.stype) SM.t ref = ref SM.empty

let rec puretoptrM (tin : Pure.mtype) : Dest.mtype =
  match tin with
  | Pure.MVar x -> ref (Dest.MVarU x)
  | Pure.Comp (c,args) -> Dest.mkcomp c (List.map args 
                                                  (function
                                                  | `A a -> 
                                                    if SM.mem !sessionQs (snd a)
                                                    then `S (puretoptrS (Pure.SComp(fst a,snd a,[])))
                                                    else `M (puretoptrM (Pure.Comp(snd a,[])))
                                                  | `M m -> `M (puretoptrM m)
                                                  | `S s -> `S (puretoptrS s)))
  | Pure.MonT (Some sx,ss) -> Dest.mkmon (Some (puretoptrS sx))
                                              (List.map ss (fun x -> puretoptrS x))
  | Pure.MonT (None,ss) -> Dest.mkmon (None) (List.map ss (fun x -> puretoptrS x))
and puretoptrS (tin_in : Pure.stype) : Dest.stype = 
  let rec go (tin : Pure.stype) (env : Dest.stype SM.t) : Dest.stype =
    match tin with
    | Pure.TyInD (mode,m,s) -> Dest.mkind mode (puretoptrM m) (go s env)
    | Pure.TyOutD (mode,m,s) -> Dest.mkoutd mode (puretoptrM m) (go s env)
    | Pure.TyInC (m,s1,s2) -> Dest.mkinc m (go s1 env) (go s2 env)
    | Pure.TyOutC (m,s1,s2) -> Dest.mkoutc m (go s1 env) (go s2 env)
    | Pure.Stop mode -> Dest.mkstop mode
    | Pure.SComp (l,c,args) -> (* This feels like it might be best as a separate function *)
        let (qs,t) = if SM.mem !sessionDefs c
                     then SM.find_exn !sessionDefs c
                     else errr l ("Undefined session type "^c)
        in if not (List.length args = List.length qs)
           then errr l ("Number of arguments, "^string_of_int (List.length args) ^", to "
                       ^c^" doesn't match its expectation of "^string_of_int (List.length qs)^"");
            let subM,subS = List.fold2_exn qs args ~init:(SM.empty,TM.empty)
              ~f:(fun (accm,accs) q amb ->
                 match q,amb with (* TODO wfS/wfM checks here *)
                 | `S x,`S s -> let s' = puretoptrS s
                                in (accm,TM.add accs x s')
                 | `S x,`A a -> let s' = puretoptrS (Pure.SComp (fst a,snd a,[]))
                                in (accm,TM.add accs x s')
                 | `M x,`A a -> let m' = (puretoptrM (Pure.Comp (snd a,[])))
                                in (SM.add accm x m',accs)
                 | `M x,`M m -> let m' = (puretoptrM m)
                                in (SM.add accm x m',accs)
                 | `M _,`S s -> (* TODO print this with a line number *)
                                failwith ("tried to instantiate data type variable"
                                                ^" with session type "^Pure.string_of_stype s)
                 | _ -> failwith "BUG puretoptrS.go SComp"
                 )
            in Dest.substS t subM subS
    | Pure.Mu ((l,x),s,name,args) -> 
      let qs = (if SM.mem !sessionQs name
               then SM.find_exn !sessionQs name
               else failwith ("Undefined session type "^name)) (* TODO print location *)
      and a = Dest.mksvar ()
      in let t = go s (SM.add env x a)
         in let args' = List.map2_exn qs args
                        ~f:(fun q arg -> match q,arg with
                                         | `M _,`M x -> `M (puretoptrM x)
                                         | `M _,`A x -> `M (puretoptrM (Pure.Comp (snd x,[])))
                                         | `S _,`A x -> `S (puretoptrS (Pure.SComp (fst x,snd x,[])))
                                         | `S _,`S x -> `S (puretoptrS x)
                                         | _ -> failwith "BUG puretoptrS.go Mu")
            in a := Dest.SComp (t,name,args');
               t
    | Pure.SVar (l,(mode,x)) ->
                if SM.mem env x
                then SM.find_exn env x
                else ref (Dest.SVarU (mode,x))
    | Pure.Intern (mode,c) -> Dest.mkint mode (LM.map c (fun s -> go s env))
    | Pure.Extern (mode,c) -> Dest.mkext mode (LM.map c (fun s -> go s env))
    | Pure.Forall (m,x,s) -> ref (Dest.Forall (m,x,puretoptrS s))
    | Pure.Exists (m,x,s) -> ref (Dest.Exists (m,x,puretoptrS s))
    | Pure.ShftUp (m,s) -> ref (Dest.ShftUp (m,puretoptrS s))
    | Pure.ShftDw (m,s) -> ref (Dest.ShftDw (m,puretoptrS s))
    | Pure.Bang s ->
      (match compare Intuist (Pure.getmode s) with
      | -1 -> ref (Dest.ShftDw (Intuist,puretoptrS s))
      | 1  -> ref (Dest.ShftUp (Intuist,puretoptrS s))
      | 0  -> failwith "trying to cast unrestricted to unrestricted" (* TODO Add srcloc *)
      | _  -> failwith "BUG puretoptrS doesn't understand Pervasisves.compare")
    | Pure.TyAt s ->
      (match compare Affine (Pure.getmode s) with
      | -1 -> ref (Dest.ShftDw (Affine,puretoptrS s))
      | 1  -> ref (Dest.ShftUp (Affine,puretoptrS s))
      | 0  -> failwith "trying to cast affine to affine" (* TODO Add srcloc *)
      | _  -> failwith "BUG puretoptrS doesn't understand Pervasisves.compare")
    | Pure.Prime s ->
      (match compare Linear (Pure.getmode s) with
      | -1 -> ref (Dest.ShftDw (Linear,puretoptrS s))
      | 1  -> ref (Dest.ShftUp (Linear,puretoptrS s))
      | 0  -> failwith "trying to cast linear to linear" (* TODO Add srcloc *)
      | _  -> failwith "BUG puretoptrS doesn't understand Pervasisves.compare")

  in go tin_in SM.empty
