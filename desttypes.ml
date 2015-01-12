open Base
open Core.Std

(* Our types use references to facilitate unification.
   Globally fresh variables use reference locations as their names.
   Indirection requires chasing (ideally with path compression).
   Unification cannot use weighted unions in most cases so we make no
   effort to do so in any case. *)

(* We use a constantless representation to simplify unification. *)
(* I'd like to use sets instead of lists but functors defeat me *)
(* For Intern the second map represents possibilities for widening
   the type. None means unlimited widening; Some M means only for
   variables in M. Additionally, M records the possible types that
   would need to be unified during any widening. This can't be just
   a single type since until we know that we are widening there is
   no harm in having different branches. Similarly for Extern *)
type ptype = (* TODO modality for sesvars *)
   | Poly of ([`M of string | `S of tyvar] list) * mtype (* list should only contain MVars and SVars *)
and mtype = mtype_raw ref
and mtype_raw =
   | MVar
   | MVarU of string
   | MInd of mtype
   | Comp of string * mtype list
   | MonT of stype option * stype list
and stype = stype_raw ref
and stype_raw =
   | SVar
   | SInd of stype
   | SComp of stype * string * [`M of mtype | `S of stype] list
   | InD of modality * mtype * stype
   | OutD of modality * mtype * stype
   | InC of modality * stype * stype
   | OutC of modality * stype * stype
   | Stop of modality
   | Intern of modality * stype LM.t
   | Extern of modality * stype LM.t
   | SVarU of tyvar
   | Forall of modality * tyvar * stype
   | Exists of modality * tyvar * stype
   | ShftUp of modality * stype (* Only need the target modality explicit *)
   | ShftDw of modality * stype (* Only need the target modality explicit *)
with sexp, bin_io

(* Functions that follow indirection to get the type pointed at by xtype ref. *)
let rec getMType (r : mtype) : mtype =
  match !r with
  | MInd r' -> getMType r'
  | _ -> r

let rec getSType_raw (r : stype) : stype =
  match !r with
  | SInd r' -> getSType_raw r'
  | _ ->  r

let rec getSType (r : stype) : stype =
  let r' = getSType_raw r
  in match !r' with
     | SInd _ -> failwith "BUG getSType SInd"
     | SComp (r'',_,_) -> getSType r''
     | _ -> r'

(* showing types *)
let mvarNames : (mtype * string) list ref = ref []
let mvarNames_counter = ref 0
let mvarName (t : mtype) : string =
  if ass_memq t (!mvarNames)
  then assq t (!mvarNames)
  else let n = post mvarNames_counter;
       in mvarNames := (t,("x"^string_of_int n)) :: !mvarNames;
          "x"^string_of_int n
let svarNames : (stype * string) list ref = ref []
let svarNames_counter = ref 0
let svarName (t : stype) : string =
  if ass_memq t (!svarNames)
  then assq t (!svarNames)
  else let n = post svarNames_counter
       in svarNames := (t,("s"^string_of_int n)) :: !svarNames;
          "s"^string_of_int n
let pvarNames : (ptype * string) list ref = ref []
let pvarNames_counter = ref 0
let pvarName (t : ptype) : string =
  if ass_memq t (!pvarNames)
  then assq t (!pvarNames)
  else let n = post pvarNames_counter
       in pvarNames := (t,("p"^string_of_int n)) :: !pvarNames;
          "p"^string_of_int n
let muvarNames : (stype * string) list ref = ref []
let muvarNames_counter = ref 0
let muvarName (t : stype) : string =
  if ass_memq t (!muvarNames)
  then assq t (!muvarNames)
  else let n = post muvarNames_counter;
       in muvarNames := (t,("m"^string_of_int n)) :: !muvarNames;
          "m"^string_of_int n

(* TODO Use intercal here *)
let rec string_of_mtype (tin : mtype) : string =
  match !(getMType tin) with
  | MInd _ -> failwith "string_of_mtype: MInd after getMType"
  | MVar -> "?"^mvarName (getMType tin)
  | MVarU s -> s
  | Comp(c,args) -> let rec go l =
                      match l with
                      | [] -> ")"
                      | [x] -> string_of_mtype x ^ ")"
                      | x::xs -> string_of_mtype x ^ ", " ^ go xs
                    in (match c,args with
                       | "[]",[a] -> "["^string_of_mtype a^"]"
                       | ",",[a;b] -> "("^string_of_mtype a^","^string_of_mtype b^")"
                       | "->",[a;b] -> "("^string_of_mtype a^")->("^string_of_mtype b^")"
                       | _ -> if List.length args = 0
                              then c
                              else c^"("^go args)
  | MonT(Some s,sm) -> let rec go l =
                    match l with
                    | [] -> "}"
                    | [x] -> go' x^"}"
                    | x::xs -> go' x^ "; " ^ go xs
                  and go' sx = string_of_stype_raw sx []
                  in if List.length sm = 0
                     then "{"^go' s^"}"
                     else  "{"^go' s^" <- "^go sm
  | MonT(None,sm) -> let rec go l =
                    match l with
                    | [] -> "}"
                    | [x] -> go' x^"}"
                    | x::xs -> go' x^ "; " ^ go xs
                  and go' sx = string_of_stype_raw sx []
                  in if List.length sm = 0
                     then "{}"
                     else  "{ <- "^go sm
(* assumes that anything in vs has been bound previously.
   x |-> "" means that x was never encountered again  *)
and string_of_stype_raw (tin:stype) (vs:(stype*string ref) list): string =
  let t = getSType_raw tin
  in if ass_memq t vs
     then let s = muvarName t in (assq t vs) := s; s
     else let n = ref "" in
          match !t with
          | SInd _ -> failwith "string_of_stype: SInd after getSType"
          | SComp (_,name,ms) -> name^" "^intercal (fun x -> match x with
                                                             | `M m -> string_of_mtype m
                                                             | `S s -> string_of_stype_raw s ((t,n)::vs)) 
                                                   " " ms
          | SVar -> "?"^svarName t
          | Stop _ -> "1"
          | OutD(_,m,s) -> 
            let s = string_of_mtype m ^ "/\\"^string_of_stype_raw s ((t,n)::vs) in
            if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | InD (_,m,s) ->
            let s = string_of_mtype m ^ "=>"^string_of_stype_raw s ((t,n)::vs) in
            if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | OutC (m,a,b) ->
            let s = string_of_stype_raw a ((t,n)::vs) ^ "*"^string_of_stype_raw b ((t,n)::vs) in
            if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | InC (m,a,b) ->
            let s = string_of_stype_raw a ((t,n)::vs) ^ "-o"^string_of_stype_raw b ((t,n)::vs) in
            if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | Intern (_,c) -> 
            let s = "+{"^intercal (fun (l,a) -> string_of_label l^": "^string_of_stype_raw a ((t,n)::vs))
                                           "; " (LM.to_alist c)^"}"
            in if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | Extern (_,c) -> 
            let s = "&{"^intercal (fun (l,a) -> string_of_label l^": "^string_of_stype_raw a ((t,n)::vs))
                                           "; " (LM.to_alist c)^"}"
            in if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | SVarU x -> string_of_tyvar x
          | Forall (_,x,s) -> "forall "^string_of_tyvar x^".("^string_of_stype_raw s ((t,n)::vs)^")" (* TODO modes *)
          | Exists (_,x,s) -> "exists "^string_of_tyvar x^".("^string_of_stype_raw s ((t,n)::vs)^")" (* TODO modes *)
          | ShftUp (m,a) -> let s = modetag m^"(" ^ string_of_stype_raw a ((t,n)::vs)^")"
                            in if !n = "" then s else "mu "^(!n)^"."^s
          | ShftDw (m,a) -> let s = modetag m^"(" ^ string_of_stype_raw a ((t,n)::vs)^")"
                            in if !n = "" then s else "mu "^(!n)^"."^s
let string_of_stype (tin : stype) : string = string_of_stype_raw tin []
let  string_of_ptype (tin : ptype) : string =
  match tin with
  | Poly(qs,m) -> if List.length qs = 0
                   then string_of_mtype m
                   else "forall " ^intercal (fun x -> match x with
                                                      | `M v -> v
                                                      | `S v -> string_of_tyvar v) " " qs
                        ^"."^string_of_mtype m

(* Get the modality information in each type *)
let getMode (sin:stype) : modality =
  match !(getSType sin) with
  | SInd _ -> failwith "BUG SInd after getSType destype getMode"
  | SComp _ -> failwith "BUG SComp after getSType destype getMode"
  | Stop m -> m
  | SVar -> failwith "BUG getMode SVar"
  | SVarU _ -> Linear (* TODO Modality *)
  | InD (m,_,_) -> m
  | OutD (m,_,_) -> m
  | InC (m,_,_) -> m
  | OutC (m,_,_) -> m
  | Intern (m,_) -> m
  | Extern (m,_) -> m
  | Forall (m,_,_) -> m
  | Exists (m,_,_) -> m
  | ShftUp (m,_) -> m
  | ShftDw (m,_) -> m

(* Wrappers to make constructing types easier *)
let mkvar () = ref MVar
let mksvar () = ref SVar
let mkcomp c args = ref (Comp (c,args))
let mkfun a b = mkcomp "->" [a;b]
let inttype = mkcomp "Int" []
let floattype = mkcomp "Float" []
let booltype = mkcomp "Bool" []
let unittype = mkcomp "()" []
let stringtype = mkcomp "String" []
let mkmon s cm = ref (MonT(s,cm))
let mkstop m = ref (Stop m)
let poly m = ref (Poly ([],m))
let mkoutd m p s = ref (OutD (m,p,s))
let mkind m p s = ref (InD (m,p,s))
let mkoutc m p s = ref (OutC (m,p,s))
let mkinc m p s = ref (InC (m,p,s))
let mkmu (f : stype -> stype) =
  let a = mksvar() in let b = f a in a := !b; b
let mkint m c = ref (Intern (m,c))
let mkext m c = ref (Extern (m,c))

(* TODO Remove this? *)
let rec freeMVars (tin : mtype) : mtype list =
  match !(getMType tin) with
  | MInd _ -> failwith "freeMVars: MInd after getMType"
  | MVar -> [getMType tin]
  | MVarU _ -> [getMType tin]
  | Comp(_,args) -> List.concat_map args freeMVars
  | MonT (s1,sm) -> (Option.value_map s1 ~default:[] ~f:(fun x -> freeMVars_S x []) )
                    @ List.concat_map sm (fun s -> freeMVars_S s [])

and freeMVars_S (tin : stype) (vs : stype list) : mtype list =
 if memq tin vs then []
 else match !(getSType tin) with
      | SInd _ -> failwith "freeMVars_S: SInd after getSType"
      | SComp _ -> failwith "freeMVars_S: SComp after getSType"
      | SVar -> []
      | Stop _ -> []
      | OutD (_,t,s) -> freeMVars t @ freeMVars_S s (tin::vs)
      | InD (_,t,s) -> freeMVars t @ freeMVars_S s (tin::vs)
      | InC (_,a,b) -> freeMVars_S a (tin::vs) @ freeMVars_S b (tin::vs)
      | OutC (_,a,b) -> freeMVars_S a (tin::vs) @ freeMVars_S b (tin::vs)
      | Intern (_,c) -> LM.fold c ~init:[] ~f:(fun ~key:_ ~data:s a -> freeMVars_S s (tin::vs) @ a)
      | Extern (_,c) -> LM.fold c ~init:[] ~f:(fun ~key:_ ~data:s a -> freeMVars_S s (tin::vs) @ a)
      | SVarU _ -> []
      | Forall (_,_,s) -> freeMVars_S s (tin::vs)
      | Exists (_,_,s) -> freeMVars_S s (tin::vs)
      | ShftUp (_,s) -> freeMVars_S s (tin::vs)
      | ShftDw (_,s) -> freeMVars_S s (tin::vs)
(* and freeMVars_P (tin : ptype) : mtype list = 
  match tin with
  | Poly (vs,_,t) -> diffq (freeMVars t) vs *)

(* We cannot just replace the bound variables with new ones
   since that would make our reference type get overwritten
   in future unifications *)
let rec instantiate (t : mtype) (vs : (mtype * mtype) list) (ss : (stype * stype) list): mtype =
  match !(getMType t) with
  | MInd _ -> failwith "instantiate: MInd after getMType"
  | MVar -> if ass_memq (getMType t) vs
            then assq (getMType t) vs
            else getMType t
  | MVarU _ -> if ass_memq (getMType t) vs
               then assq (getMType t) vs
               else getMType t
  | Comp (c,args) -> ref (Comp(c,List.map args (fun a -> instantiate a vs ss)))
  | MonT (Some s,sargs) -> ref (MonT(Some (instantiate_S s vs ss)
                                    ,List.map sargs (fun a -> instantiate_S a vs ss)))
  | MonT (None,sargs) -> ref (MonT(None ,List.map sargs (fun a -> instantiate_S a vs ss)))
(* To avoid unfolding mu's too much this gets super ugly *)
(* I'm pretty sure the case for SVar is wrong, but I don't
   know what I should do. *)
and instantiate_S (tin:stype) (vs:(mtype * mtype) list) (ss:(stype*stype) list) : stype =
  if List.length vs = 0 && List.length ss = 0
  then tin
  else 
  let t = getSType tin
  in if ass_memq t ss
     then assq t ss
     else match !t with
          | SInd _ -> failwith "BUG instantiate_S: SInd after getSType"
          | SComp _ -> failwith "BUG instantiate_S: SInd after getSType"
          | Stop m -> mkstop m
          | SVar -> t
          | SVarU _ -> t
          | OutD (mode,m,s) -> 
                          let a = mksvar()
                          in let b = mkoutd mode (instantiate m vs ss) a
                          in a := SInd (instantiate_S s vs ((t,b)::ss));
                             b
          | InD (mode,m,s)  -> 
                          let a = mksvar()
                          in let b = mkind mode (instantiate m vs ss) a
                          in a := SInd (instantiate_S s vs ((t,b)::ss));
                             b
          | OutC (m,x,y) -> let a,b = mksvar(),mksvar()
                            in b := SInd (mkoutc m (instantiate_S x vs ([t,b]@ss)) a);
                               a := SInd (instantiate_S y vs ([t,b]@ss));
                               b
          | InC  (m,x,y) -> let a,b = mksvar(),mksvar()
                            in b := SInd (mkinc m (instantiate_S x vs ([t,b]@ss)) a);
                               a := SInd (instantiate_S y vs ([t,b]@ss));
                               b
          | Intern (m,c) -> let b = mksvar()
                        in b := SInd (mkint m (LM.map c (fun x -> instantiate_S x vs ([t,b]@ss))));
                           b
          | Extern (m,c) -> let b = mksvar()
                        in b := SInd (mkext m (LM.map c (fun x -> instantiate_S x vs ([t,b]@ss))));
                           b
          | Forall (m,x,s) -> let a = mksvar()
                            in a := SInd (ref (Forall (m,x,(instantiate_S s vs ([t,a]@ss)))));
                               a
          | Exists (m,x,s) -> let a = mksvar()
                            in a := SInd (ref (Exists (m,x,(instantiate_S s vs ([t,a]@ss)))));
                               a
          | ShftUp (m,s) -> let a = mksvar()
                            in a := SInd (ref (ShftUp (m,(instantiate_S s vs ([t,a]@ss)))));
                               a
          | ShftDw (m,s) -> let a = mksvar()
                            in a := SInd (ref (ShftDw (m,(instantiate_S s vs ([t,a]@ss)))));
                               a
  
(* Do we need to avoid capturing in instantiate_P?  Currently we don't try. *)
(* and instantiate_P (t : ptype) (vs : (mtype * mtype) list) 
                              (ss : (stype * stype) list) : ptype =
  match t with
  | Poly (qs,m) -> (Poly (qs,instantiate m (List.fold_left qs ~init:vs ~f:(fun l x -> ass_removeq x l))
                                             ss))
*)

(* Find the free session type variables. TODO this looks incomplete. *)
(* TODO why does this returns a list and not a set? *)
let rec freeSUM_ (min:mtype) (vm: mtype list) (vs: stype list) : string list =
  let t = getMType min in if memq t vm then [] else
  match !t with
  | MInd _ -> failwith "BUG. freeSUM_ MInd"
  | Comp (_,args) -> List.fold_left args ~init:[] ~f:(fun acc a -> freeSUM_ a (t::vm) vs @ acc)
  | MVarU _ -> []
  | MVar -> []
  | MonT (Some s,ss) -> (freeSUS_ s (t::vm) vs) @ (List.concat_map ss (fun x -> freeSUS_ x (t::vm) vs))
  | MonT (None,ss) -> (List.concat_map ss (fun x -> freeSUS_ x (t::vm) vs))
and freeSUS_ (sin:stype) (vm: mtype list) (vs: stype list) : string list =
  let t = getSType sin in if memq t vs then [] else
  match !t with
  | SInd _ -> failwith "BUG. freeSUS_ SInd"
  | SComp _ -> failwith "BUG. freeSUS_ SComp"
  | SVar -> failwith "BUG. freeSUS_ SVar"
  | Stop _ -> []
  | SVarU (_,x) -> [x]
  | OutD (_,m,s) -> freeSUM_ m vm (t::vs) @ freeSUS_ s vm (t::vs)
  | InD (_,m,s) -> freeSUM_ m vm (t::vs) @ freeSUS_ s vm (t::vs)
  | InC (_,s1,s2) -> freeSUS_ s1 vm (t::vs) @ freeSUS_ s2 vm (t::vs)
  | OutC (_,s1,s2) -> freeSUS_ s1 vm (t::vs) @ freeSUS_ s2 vm (t::vs)
  | Extern (_,sm) -> LM.fold sm ~init:[] ~f:(fun ~key:_ ~data:s acc -> acc @ freeSUS_ s vm (t::vs))
  | Intern (_,sm) -> LM.fold sm ~init:[] ~f:(fun ~key:_ ~data:s acc -> acc @ freeSUS_ s vm (t::vs))
  | Forall (_,(_,x),s) -> List.filter (freeSUS_ s vm (t::vs)) (fun y -> not (x = y))
  | Exists (_,(_,x),s) -> List.filter (freeSUS_ s vm (t::vs)) (fun y -> not (x = y))
  | ShftUp (_,s) -> freeSUS_ s vm (t::vs)
  | ShftDw (_,s) -> freeSUS_ s vm (t::vs)

let freeSUM m = List.dedup (freeSUM_ m [] [])
let freeSUS s = List.dedup (freeSUS_ s [] [])

let rec substM_ (min:mtype) (subM:mtype SM.t) (subS:stype TM.t) 
            (vm:(mtype*mtype) list) (vs:(stype*stype) list) : mtype = 
  let t = getMType min in if ass_memq t vm then assq t vm else
  match !t with
  | MInd _ -> failwith "BUG. substM MInd"
  | Comp (c,args) -> ref (Comp(c,List.map args (fun a -> substM_ a subM subS vm vs)))
  | MonT (Some t,ts) -> ref (MonT(Some (substS_ t subM subS vm vs)
                            ,List.map ts (fun s -> substS_ s subM subS vm vs)))
  | MonT (None,ts) -> ref (MonT(None
                            ,List.map ts (fun s -> substS_ s subM subS vm vs)))
  | MVar -> min (* TODO is this really right? *)
  | MVarU x -> (match SM.find subM x with
               | Some m' -> m'
               | None -> min)
and substS_ (sin:stype) (subM:mtype SM.t) (subS:stype TM.t) 
            (vm:(mtype*mtype) list) (vs:(stype*stype) list) : stype = 
  let t = getSType_raw sin in if ass_memq t vs then assq t vs else
  match !t with
  | SInd _ -> failwith "BUG. substS SInd"
  | SVar -> failwith "BUG substS_ SVar" (* sin *)(* TODO This might be questionable *)
  | SComp (s,name,args) -> 
    let a = mksvar ()
    in a := SInd (ref (SComp (substS_ s subM subS vm ((t,a)::vs)
                             ,name
                             ,List.map args (fun x -> match x with
                                                      | `M y -> `M (substM_ y subM subS vm ((t,a)::vs))
                                                      | `S y -> `S (substS_ y subM subS vm ((t,a)::vs))))));
       a
  | Stop m -> mkstop m
  | SVarU x ->
    (match TM.find subS x with
    | Some s' -> s'
    | None -> sin)
  | InD (mode,m,s) -> 
    let a = mksvar ()
    in let b = mkind mode (substM_ m subM subS vm vs) a
       in a := SInd (substS_ s subM subS vm ([t,b]@vs));
          b
  | OutD (mode,m,s) -> 
    let a = mksvar ()
    in let b = mkoutd mode (substM_ m subM subS vm vs) a
       in a := SInd (substS_ s subM subS vm ([t,b]@vs));
          b
  | InC (m,s1,s2) -> 
    let a,b = mksvar(),mksvar()
    in b := SInd (mkinc m (substS_ s1 subM subS vm ([t,b]@vs)) a);
       a := SInd (substS_ s2 subM subS vm ([t,b]@vs));
       b
  | OutC (m,s1,s2) -> 
    let a,b = mksvar(),mksvar()
    in b := SInd (mkoutc m (substS_ s1 subM subS vm ([t,b]@vs)) a);
       a := SInd (substS_ s2 subM subS vm ([t,b]@vs));
       b
  | Forall (m,x,s) ->
    (* TODO be capture avoiding *)
    let subS' = if TM.mem subS x then TM.remove subS x else subS
    in let a = mksvar()
       in a := SInd (ref (Forall (m,x,substS_ s subM subS' vm ([t,a]@vs))));
          a
  | Exists (m,x,s) ->
    (* TODO be capture avoiding *)
    let subS' = if TM.mem subS x then TM.remove subS x else subS
    in let a = mksvar()
       in a := SInd (ref (Exists (m,x,substS_ s subM subS' vm ([t,a]@vs))));
          a
  | Intern (m,c) -> 
    let b = mksvar()
    in b := SInd (mkint m (LM.map c (fun s -> substS_ s subM subS vm ([t,b]@vs))));
       b
  | Extern (m,c) -> 
    let b = mksvar()
    in b := SInd (mkext m (LM.map c (fun s -> substS_ s subM subS vm ([t,b]@vs))));
       b
  | ShftUp (m,s) ->
    let a = mksvar()
    in a := SInd (ref (ShftUp (m,substS_ s subM subS vm ([t,a]@vs))));
       a
  | ShftDw (m,s) ->
    let a = mksvar()
    in a := SInd (ref (ShftDw (m,substS_ s subM subS vm ([t,a]@vs))));
       a

let substM m subM subS = substM_ m subM subS [] []
let substS s subM subS = substS_ s subM subS [] []

(* type decl bookeepking *)
let typeNames : SS.t ref = ref (SS.of_list ["()";"Bool";"Int"])

let conArities : int SM.t ref = ref SM.empty
let conArities_init : int SM.t = 
  SM.of_alist_exn [("True",0);
                   ("False",0); 
                   ("()",0);
                   ("::",2);
                   ("[]",0);
                   (",",2)]

(* TODO Why is this split into an explicit init phase? *)
(* fields are: mvaru names, argument types (list) * result type *)
let conTypes : (string list * mtype list * mtype) SM.t ref = ref SM.empty
let conTypes_init : (string list * mtype list * mtype) SM.t = 
  SM.of_alist_exn
  [("True",([],[],ref (Comp("Bool",[]))));
   ("False",([],[],ref (Comp("Bool",[]))));
   ("()",([],[],ref (Comp("()",[]))));
   ("::",(["a"],[ref (MVarU "a");ref (Comp("[]",[ref (MVarU "a")]))],ref (Comp("[]",[ref (MVarU "a")]))));
   ("[]",(["a"],[],ref (Comp("[]",[ref (MVarU "a")]))));
   (",",(["a";"b"],[ref (MVarU "a");ref (MVarU "b")],ref (Comp(",",[ref (MVarU "a");ref (MVarU "b")]))))]

let conTypeNames : string SM.t ref = ref SM.empty
let conTypeNames_init : string SM.t =
  SM.of_alist_exn
  [("True","Bool");
   ("False","Bool");
   ("()","()");
   ("::","[]");
   ("[]","[]");
   (",",",")]


let reinit () : unit =
    conArities := conArities_init;
    conTypes := conTypes_init;
    conTypeNames := conTypeNames_init
    
(* After generating a fresh instance we return the list of its argument types
   and its ADT. All of which have had fresh unifiable variables
   substituted for the bound variables. *)
let conInstance (c : string) : (mtype list * mtype) =
  if not (SM.mem !conTypes c) then failwith ("BUG unbound constructor: "^c);
  let (qs,args,result) = SM.find_exn !conTypes c
  in let subM = SM.of_alist_exn (List.map qs (fun v -> (v,ref MVar)))
     in (List.map args (fun a -> substM a subM TM.empty)
        ,substM result subM TM.empty)
