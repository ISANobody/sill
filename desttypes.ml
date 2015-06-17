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
(* TODO handle modalities more implicitly *)
type ptype = (* TODO modality for sesvars *)
   | Poly of string list * tyvar list * mtype
and mtype = mtype_raw ref
and mtype_raw =
   | MVar
   | MVarU of string
   | MInd of mtype
   | Comp of string * [`M of mtype | `S of stype] list
   | MonT of stype option * stype list
and stype = stype_raw ref
and stype_raw =
   | SVar
   | SInd of stype
   | SComp of srcloc * stype * string * [`M of mtype | `S of stype] list
   | InD of srcloc * modality * mtype * stype
   | OutD of srcloc * modality * mtype * stype
   | InC of srcloc * modality * stype * stype
   | OutC of srcloc * modality * stype * stype
   | Stop of srcloc * modality
   | Intern of srcloc * modality * stype LM.t
   | Extern of srcloc * modality * stype LM.t
   | SVarU of srcloc * tyvar
   | Forall of srcloc * modality * tyvar * stype
   | Exists of srcloc * modality * tyvar * stype
   | ShftUp of srcloc * modality * stype (* Only need the target modality explicit *)
   | ShftDw of srcloc * modality * stype (* Only need the target modality explicit *)
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
     | SComp (_,r'',_,_) -> getSType r''
     | _ -> r'

let locS (s: stype) : srcloc =
  match !(getSType s) with
  | SInd _ -> failwith "locS: SInd after getSType"
  | SVar -> failwith "locS: SInd after getSType"
  | Stop (i,_) -> i
  | SComp (i,_,_,_) -> i
  | InD (i,_,_,_) -> i
  | OutD (i,_,_,_) -> i
  | InC (i,_,_,_) -> i
  | OutC (i,_,_,_) -> i
  | Intern (i,_,_) -> i
  | Extern (i,_,_) -> i
  | SVarU (i,_) -> i
  | Forall (i,_,_,_) -> i
  | Exists (i,_,_,_) -> i
  | ShftUp (i,_,_) -> i
  | ShftDw (i,_,_) -> i

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
  | Comp(c,args) ->
    (match c,args with
    | "[]",[`M a] -> "["^string_of_mtype a^"]"
    | ",",[`M a;`M b] -> "("^string_of_mtype a^","^string_of_mtype b^")"
    | "->",[`M a;`M b] -> "("^string_of_mtype a^")->("^string_of_mtype b^")"
    | _ -> if List.length args = 0
           then c
           else c^"("^intercal (function
                               | `M m -> string_of_mtype m
                               | `S s -> string_of_stype_raw s []) ", " args^")")
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
          | SComp (_,_,name,ms) -> name^" "^intercal (fun x -> match x with
                                                             | `M m -> string_of_mtype m
                                                             | `S s -> string_of_stype_raw s ((t,n)::vs)) 
                                                   " " ms
          | SVar -> "?"^svarName t
          | Stop _ -> "1"
          | OutD(_,_,m,s) -> 
            let s = string_of_mtype m ^ "/\\"^string_of_stype_raw s ((t,n)::vs) in
            if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | InD (_,_,m,s) ->
            let s = string_of_mtype m ^ "=>"^string_of_stype_raw s ((t,n)::vs) in
            if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | OutC (_,m,a,b) ->
            let s = string_of_stype_raw a ((t,n)::vs) ^ "*"^string_of_stype_raw b ((t,n)::vs) in
            if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | InC (_,m,a,b) ->
            let s = string_of_stype_raw a ((t,n)::vs) ^ "-o"^string_of_stype_raw b ((t,n)::vs) in
            if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | Intern (_,_,c) -> 
            let s = "+{"^intercal (fun (l,a) -> string_of_label l^": "^string_of_stype_raw a ((t,n)::vs))
                                           "; " (LM.to_alist c)^"}"
            in if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | Extern (_,_,c) -> 
            let s = "&{"^intercal (fun (l,a) -> string_of_label l^": "^string_of_stype_raw a ((t,n)::vs))
                                           "; " (LM.to_alist c)^"}"
            in if !n = ""
            then s
            else "mu "^(!n)^"."^s
          | SVarU (_,x) -> string_of_tyvar x
          | Forall (_,_,x,s) -> "forall "^string_of_tyvar x^".("^string_of_stype_raw s ((t,n)::vs)^")" (* TODO modes *)
          | Exists (_,_,x,s) -> "exists "^string_of_tyvar x^".("^string_of_stype_raw s ((t,n)::vs)^")" (* TODO modes *)
          | ShftUp (_,m,a) -> let s = modetag m^"(" ^ string_of_stype_raw a ((t,n)::vs)^")"
                            in if !n = "" then s else "mu "^(!n)^"."^s
          | ShftDw (_,m,a) -> let s = modetag m^"(" ^ string_of_stype_raw a ((t,n)::vs)^")"
                            in if !n = "" then s else "mu "^(!n)^"."^s
let string_of_stype (tin : stype) : string = string_of_stype_raw tin []
let  string_of_ptype (tin : ptype) : string =
  match tin with
  | Poly(mvs,svs,m) -> 
    if List.length mvs = 0 && List.length svs = 0
    then string_of_mtype m
    else "forall " ^intercal (fun x -> x) " " mvs
         ^intercal string_of_tyvar " " svs ^"."^string_of_mtype m

(* Get the modality information in each type *)
let getMode (sin:stype) : modality =
  match !(getSType sin) with
  | SInd _ -> failwith "BUG SInd after getSType destype getMode"
  | SComp _ -> failwith "BUG SComp after getSType destype getMode"
  | Stop (_,m) -> m
  | SVar -> failwith "BUG getMode SVar"
  | SVarU (_,(m,_)) -> m
  | InD (_,m,_,_) -> m
  | OutD (_,m,_,_) -> m
  | InC (_,m,_,_) -> m
  | OutC (_,m,_,_) -> m
  | Intern (_,m,_) -> m
  | Extern (_,m,_) -> m
  | Forall (_,m,_,_) -> m
  | Exists (_,m,_,_) -> m
  | ShftUp (_,m,_) -> m
  | ShftDw (_,m,_) -> m

let polarity (sin:stype) : [`Pos | `Neg] =
  match !(getSType sin) with
  | SInd _ -> failwith "BUG SInd after getSType desttypes.polarity"
  | SComp _ -> failwith "BUG SComp after getSType desttypes.polarity"
  | SVar -> failwith "BUG desttypes.polarity SVar"
  | SVarU _ -> `Pos
  | Stop _ -> `Pos
  | InD _ -> `Neg
  | OutD _ -> `Pos
  | InC _ -> `Neg
  | OutC _ -> `Pos
  | Intern _ -> `Pos
  | Extern _ -> `Neg
  | Forall _ -> `Neg
  | Exists _ -> `Pos
  | ShftUp _ -> `Neg
  | ShftDw _ -> `Pos
  

(* Wrappers to make constructing types easier *)
let mkvar () = ref MVar
let mksvar () = ref SVar
let mkcomp c args = ref (Comp (c,args))
let mkfun a b : mtype = mkcomp "->" [`M a;`M b]
let inttype = mkcomp "Int" []
let floattype = mkcomp "Float" []
let booltype = mkcomp "Bool" []
let unittype = mkcomp "()" []
let stringtype = mkcomp "String" []
let mkmon s cm = ref (MonT(s,cm))
let mkstop l m = ref (Stop (l,m))
let poly m = ref (Poly ([],[],m))
let mkoutd l m p s = ref (OutD (l,m,p,s))
let mkind l m p s = ref (InD (l,m,p,s))
let mkoutc l m p s = ref (OutC (l,m,p,s))
let mkinc l m p s = ref (InC (l,m,p,s))
let mkint l m c = ref (Intern (l,m,c))
let mkext l m c = ref (Extern (l,m,c))

(* TODO Remove this? *)
let rec freeMVars (tin : mtype) : mtype list =
  match !(getMType tin) with
  | MInd _ -> failwith "freeMVars: MInd after getMType"
  | MVar -> [getMType tin]
  | MVarU _ -> [getMType tin]
  | Comp(_,args) -> List.concat_map args (function
                                         | `M m -> freeMVars m
                                         | `S s -> freeMVars_S s [])
  | MonT (s1,sm) -> (Option.value_map s1 ~default:[] ~f:(fun x -> freeMVars_S x []) )
                    @ List.concat_map sm (fun s -> freeMVars_S s [])

and freeMVars_S (tin : stype) (vs : stype list) : mtype list =
 if memq tin vs then []
 else match !(getSType tin) with
      | SInd _ -> failwith "freeMVars_S: SInd after getSType"
      | SComp _ -> failwith "freeMVars_S: SComp after getSType"
      | SVar -> []
      | Stop _ -> []
      | OutD (_,_,t,s) -> freeMVars t @ freeMVars_S s (tin::vs)
      | InD (_,_,t,s) -> freeMVars t @ freeMVars_S s (tin::vs)
      | InC (_,_,a,b) -> freeMVars_S a (tin::vs) @ freeMVars_S b (tin::vs)
      | OutC (_,_,a,b) -> freeMVars_S a (tin::vs) @ freeMVars_S b (tin::vs)
      | Intern (_,_,c) -> LM.fold c ~init:[] ~f:(fun ~key:_ ~data:s a -> freeMVars_S s (tin::vs) @ a)
      | Extern (_,_,c) -> LM.fold c ~init:[] ~f:(fun ~key:_ ~data:s a -> freeMVars_S s (tin::vs) @ a)
      | SVarU _ -> []
      | Forall (_,_,_,s) -> freeMVars_S s (tin::vs)
      | Exists (_,_,_,s) -> freeMVars_S s (tin::vs)
      | ShftUp (_,_,s) -> freeMVars_S s (tin::vs)
      | ShftDw (_,_,s) -> freeMVars_S s (tin::vs)

(* Find the free session type variables. TODO this looks incomplete. *)
(* TODO why does this returns a list and not a set? *)
let rec freeSUM_ (min:mtype) (vm: mtype list) (vs: stype list) : string list =
  let t = getMType min in if memq t vm then [] else
  match !t with
  | MInd _ -> failwith "BUG. freeSUM_ MInd"
  | Comp (_,args) -> List.fold_left args ~init:[] ~f:(fun acc -> function
                                                     | `M m -> freeSUM_ m (t::vm) vs @ acc
                                                     | `S s -> freeSUS_ s (t::vm) vs @ acc)
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
  | SVarU (_,(_,x)) -> [x]
  | OutD (_,_,m,s) -> freeSUM_ m vm (t::vs) @ freeSUS_ s vm (t::vs)
  | InD (_,_,m,s) -> freeSUM_ m vm (t::vs) @ freeSUS_ s vm (t::vs)
  | InC (_,_,s1,s2) -> freeSUS_ s1 vm (t::vs) @ freeSUS_ s2 vm (t::vs)
  | OutC (_,_,s1,s2) -> freeSUS_ s1 vm (t::vs) @ freeSUS_ s2 vm (t::vs)
  | Extern (_,_,sm) -> LM.fold sm ~init:[] ~f:(fun ~key:_ ~data:s acc -> acc @ freeSUS_ s vm (t::vs))
  | Intern (_,_,sm) -> LM.fold sm ~init:[] ~f:(fun ~key:_ ~data:s acc -> acc @ freeSUS_ s vm (t::vs))
  | Forall (_,_,(_,x),s) -> List.filter (freeSUS_ s vm (t::vs)) (fun y -> not (x = y))
  | Exists (_,_,(_,x),s) -> List.filter (freeSUS_ s vm (t::vs)) (fun y -> not (x = y))
  | ShftUp (_,_,s) -> freeSUS_ s vm (t::vs)
  | ShftDw (_,_,s) -> freeSUS_ s vm (t::vs)

let freeSUM m = List.dedup (freeSUM_ m [] [])
let freeSUS s = List.dedup (freeSUS_ s [] [])

let rec substM_ (min:mtype) (subM:mtype SM.t) (subS:stype TM.t) 
            (vm:(mtype*mtype) list) (vs:(stype*stype) list) : mtype = 
  let t = getMType min in if ass_memq t vm then assq t vm else
  match !t with
  | MInd _ -> failwith "BUG. substM MInd"
  | Comp (c,args) -> ref (Comp(c,List.map args (function
                                               | `M a -> `M (substM_ a subM subS vm vs)
                                               | `S a -> `S (substS_ a subM subS vm vs))))
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
  | SComp (l,s,name,args) -> 
    let a = mksvar ()
    in a := SInd (ref (SComp (l,substS_ s subM subS vm ((t,a)::vs)
                             ,name
                             ,List.map args (fun x -> match x with
                                                      | `M y -> `M (substM_ y subM subS vm ((t,a)::vs))
                                                      | `S y -> `S (substS_ y subM subS vm ((t,a)::vs))))));
       a
  | Stop (l,m) -> mkstop l m
  | SVarU (_,x) ->
    (match TM.find subS x with
    | Some s' -> s'
    | None -> sin)
  | InD (l,mode,m,s) -> 
    let a = mksvar ()
    in let b = mkind l mode (substM_ m subM subS vm vs) a
       in a := SInd (substS_ s subM subS vm ([t,b]@vs));
          b
  | OutD (l,mode,m,s) -> 
    let a = mksvar ()
    in let b = mkoutd l mode (substM_ m subM subS vm vs) a
       in a := SInd (substS_ s subM subS vm ([t,b]@vs));
          b
  | InC (l,m,s1,s2) -> 
    let a,b = mksvar(),mksvar()
    in b := SInd (mkinc l m (substS_ s1 subM subS vm ([t,b]@vs)) a);
       a := SInd (substS_ s2 subM subS vm ([t,b]@vs));
       b
  | OutC (l,m,s1,s2) -> 
    let a,b = mksvar(),mksvar()
    in b := SInd (mkoutc l m (substS_ s1 subM subS vm ([t,b]@vs)) a);
       a := SInd (substS_ s2 subM subS vm ([t,b]@vs));
       b
  | Forall (l,m,x,s) ->
    (* TODO be capture avoiding *)
    let subS' = if TM.mem subS x then TM.remove subS x else subS
    in let a = mksvar()
       in a := SInd (ref (Forall (l,m,x,substS_ s subM subS' vm ([t,a]@vs))));
          a
  | Exists (l,m,x,s) ->
    (* TODO be capture avoiding *)
    let subS' = if TM.mem subS x then TM.remove subS x else subS
    in let a = mksvar()
       in a := SInd (ref (Exists (l,m,x,substS_ s subM subS' vm ([t,a]@vs))));
          a
  | Intern (l,m,c) -> 
    let b = mksvar()
    in b := SInd (mkint l m (LM.map c (fun s -> substS_ s subM subS vm ([t,b]@vs))));
       b
  | Extern (l,m,c) -> 
    let b = mksvar()
    in b := SInd (mkext l m (LM.map c (fun s -> substS_ s subM subS vm ([t,b]@vs))));
       b
  | ShftUp (l,m,s) ->
    let a = mksvar()
    in a := SInd (ref (ShftUp (l,m,substS_ s subM subS vm ([t,a]@vs))));
       a
  | ShftDw (l,m,s) ->
    let a = mksvar()
    in a := SInd (ref (ShftDw (l,m,substS_ s subM subS vm ([t,a]@vs))));
       a

let substM m subM subS = substM_ m subM subS [] []
let substS s subM subS = substS_ s subM subS [] []

(* Get the continuation type of session type. Return None if there isn't exactly one. 
   I know this is bizarre, but anywhere this is needed the more than one case will need
   custom handling. *)
let contType (tin:stype) : stype option = match !(getSType tin) with
  | SInd _ -> failwith "BUG conType SInd"
  | SVar -> failwith "BUG conType SVar"
  | SVarU _ -> failwith "BUG conType SVarU"
  | SComp _ -> failwith "BUG conType SComp"
  | InD (_,_,_,s) -> Some s
  | OutD (_,_,_,s) -> Some s
  | InC (_,_,_,s) -> Some s
  | OutC (_,_,_,s) -> Some s
  | Intern _ -> None
  | Extern _ -> None
  | Stop _ -> None
  | Forall (_,_,_,s) -> Some s
  | Exists (_,_,_,s) -> Some s
  | ShftUp (_,_,s) -> None
  | ShftDw (_,_,s) -> None

(* type decl bookeepking *)
let typeNames : SS.t ref = 
        ref (SS.of_list ["()";"Bool";"Int";"Float";"String"
                        ;"[]";"->";","])

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
(* TODO Consider adding a map from type names to quantifiers. Bidir.ml's case for 'case'
        could benefit. *)
let conTypes : (string list * tyvar list * mtype list * mtype) SM.t ref = ref SM.empty
let conTypes_init : (string list * tyvar list * mtype list * mtype) SM.t = 
  SM.of_alist_exn
  [("True",([],[],[],ref (Comp("Bool",[]))));
   ("False",([],[],[],ref (Comp("Bool",[]))));
   ("()",([],[],[],ref (Comp("()",[]))));
   ("::",(["a"],[],[ref (MVarU "a");ref (Comp("[]",[`M (ref (MVarU "a"))]))],ref (Comp("[]",[`M (ref (MVarU "a"))]))));
   ("[]",(["a"],[],[],ref (Comp("[]",[`M (ref (MVarU "a"))]))));
   (",",(["a";"b"],[],[ref (MVarU "a");ref (MVarU "b")],ref (Comp(",",[`M (ref (MVarU "a"));`M (ref (MVarU "b"))]))))]

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
(* TODO the `S error message is terrible *)
let conInstance (c : string) : (mtype list * mtype) =
  if not (SM.mem !conTypes c) then failwith ("BUG unbound constructor: "^c);
  let (mvs,svs,args,result) = SM.find_exn !conTypes c
  in if not (svs = []) then failwith "BUG conInstance svs";
     let subM = SM.of_alist_exn (List.map mvs (fun v -> (v,ref MVar)))
     in (List.map args (fun a -> substM a subM TM.empty)
        ,substM result subM TM.empty)
