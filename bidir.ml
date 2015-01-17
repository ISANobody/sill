open Base
open Types.Dest
open Syntax.Core
open Vars
open Unify
open Connection
open Subtype
open Core.Std

(* When converting 1L usages into a structural congruence we exploit the idea that
   Resource Management is tagging channels as being slack in an all or nothing fashion
   where we would like to now be a bit more precise *)

type funenv = ptype FM.t
type sesenv = stype CM.t

(* Type to represent whether a channel was either fully Consumed, fully Unconsumed, or
Slack-ly consumed *)

type consumed = Consumed | Slack | Unconsumed
let string_of_consumed (c:consumed) : string =
  match c with
  | Consumed -> "Consumed"
  | Slack -> "Slack"
  | Unconsumed -> "Unconsumed"

(* Making this just a global reference sounds like a bad idea, but seems to be how Honda
   treats stuff *)
let sessions : stype FM.t ref = ref FM.empty

let keyset (cm:'a CM.t) : CS.t = CM.fold cm ~init:CS.empty ~f:(fun ~key:k ~data:_ a -> CS.add a k)
let subset (s1: CS.t) (s2:CS.t) : bool = CS.is_empty (CS.diff s1 s2)

(* Does gkind dependent sorting of channels into consumed and slack *)
let findResidual (env:sesenv) : consumed CM.t =
  let slkmap = match !global_channel_kind with
    | "linear" -> CM.mapi env (fun ~key:k ~data:_ -> if not (is_lin k)
                                                     then Slack
                                                     else Unconsumed)
    (* TODO Should we do something with modes here? *)
    | "one_weaken" ->  CM.mapi env ~f:(fun ~key:k ~data:t -> if !(Types.Dest.getSType t) = Types.Dest.Stop Linear
                                                 || not (is_lin k)
                                               then Slack
                                               else Unconsumed)
    | "affine" -> CM.map env (fun _ -> Slack)
    | _ -> failwith "Unknown gkind"
  in CM.filter_mapi slkmap (fun ~key:k ~data:d -> if is_shr k
                                                  then None
                                                  else Some d)

let unboundcheck (rule : string) (env : 'a CM.t) (c : cvar) : unit =
  if not (CM.mem env c)
  then errr (fst c) (rule^" unbound channel "^string_of_cvar c)
  else ()

let safefind (rule:string) (m:'a CM.t) (c:cvar) : 'a  =
    unboundcheck rule m c;
    CM.find_exn m c

(* Check to confirm that two channel maps have the same keys.
   Since there is no point in tracking unrestricted channels, this doesn't check for that *)
let samekeys (l:srcloc) (rule:string) (a : 'a CM.t) (b : 'b CM.t) : unit =
  CM.iter a ~f:(fun ~key:k ~data:_ -> if CM.mem b k
                                      then ()
                                      else errr l (rule^": samekeys-1 BUG on "^string_of_cvar k));
  CM.iter b ~f:(fun ~key:k ~data:_ -> if CM.mem a k
                                      then ()
                                      else errr l (rule^": samekeys-2 BUG on "^string_of_cvar k))

let notconsumed (l:srcloc) (env : sesenv) (res : consumed CM.t) : sesenv =
  samekeys l "notconsumed" env res;
  CM.filter env (fun ~key:k ~data:_ -> not (CM.find_exn res k = Consumed))

(* Error if there are any unconsumed channels *)
let allconsumed (rule:string) (res : consumed CM.t) : unit =
  CM.iter res (fun ~key:c ~data:d -> match d with
                                     | Unconsumed -> errr (fst c) ("Unconsumed channel "
                                                                  ^string_of_cvar c)
                                     | Consumed | Slack -> ())

let prettyUnifM (rule : string) (loc : srcloc) (tin1 : mtype) (tin2 : mtype) : unit =
  if !unify_trace_flag
  then print_endline ("prettyUnifM: "^rule^" "^loc2str loc^" "^string_of_mtype tin1
                     ^" === " ^string_of_mtype tin2);
  let st1 = string_of_mtype tin1
  and st2 = string_of_mtype tin2 in
  try (unifyM tin1 tin2) 
  with _ -> errr loc ("Unification failure in "^rule
            ^" failed solving "^st1
            ^" === "^st2)

let prettyUnifS (rule : string) (loc : srcloc) (tin1 : stype) (tin2 : stype) : unit =
  if !unify_trace_flag
  then print_endline ("prettyUnifS: "^rule^" "^loc2str loc^" "^string_of_stype tin1
                     ^" === "^string_of_stype tin2);
  let st1 = string_of_stype tin1
  and st2 = string_of_stype tin2 in
  try (unifyS tin1 tin2) 
  with _ -> errr loc ("Unification failure in "^rule
            ^" failed solving "^st1 ^" === "^st2)

let prettySubS (rule : string) (loc : srcloc) (tin1 : stype) (tin2 : stype) : unit =
   if !subtype_trace_flag
   then print_endline ((loc2str loc)^" "^string_of_stype tin1^" <<< "^string_of_stype tin2);
   try (subtypeS tin1 tin2 `Shallow)
   with | Failure s -> errr loc ("Unknown subtyping BUG in "^rule
            ^" failed solving "^string_of_stype tin1
            ^" <<< "^string_of_stype tin2 ^ " with error message " ^ s)
        | NonUniqS (s1,s2) -> errr loc ("Subtyping failure in "^rule
            ^" failed solving "^string_of_stype tin1
            ^" <<< "^string_of_stype tin2^" could not determine unique solution to "
            ^string_of_stype s1^" <<< "^string_of_stype s2)
        | GeneralSubtyping s -> errr loc ("Subtyping failure in "^rule
            ^" failed solving "^string_of_stype tin1
            ^" <<< "^string_of_stype tin2^": "^s)

(* A bit silly, but required to get error messages right in boundhere.
   The problem comes from passing srclocs around with cvars *)
let swapkey c (a:'a CM.t) (b:'b CM.t) : 'a CM.t =
  if not (CM.mem a c) then failwith "BUG: swapkey-a";
  if not (CM.mem b c) then failwith "BUG: swapkey-b";
  CM.fold b ~init:a ~f:(fun ~key:k ~data:_ acc -> if cvar_eq c k
                                                  then CM.add acc k (CM.find_exn a c)
                                                  else acc)

(* Helper function for rules that bind channels.
   Input: rule name; environment incoming into the rule; map tracking how channels
          were used in any subprocesses
   For a channel var bound by 'rule', check that it was used or could be absorbed. 
   If so, ensure that any shadowed channels are used later one or marked as slack *)
(* TODO Test that this correctly marks affine shadowed channels slack.
        Can't write test w/o modality tags *)
(* The last arg records the affineFree refs for all continuation processes. *)
let boundhere (rule : string) (lin:sesenv) (res:consumed CM.t) (c:cvar) 
              (frs:astinfo list) : consumed CM.t =
  if is_shr c
  then res (* unrestricted channels don't show up *)
  else match safefind rule res c with
       | Unconsumed -> errr (fst c) (rule^" Unconsumed channel "^string_of_cvar c)
       | Consumed -> if CM.mem lin c
                     then swapkey c (CM.add res c Unconsumed) lin
                     else CM.remove res c
       | Slack -> if is_aff c
                  then List.iter frs (fun x -> x.affineFrees := CS.add !(x.affineFrees) c);
                  if CM.mem lin c
                  then swapkey c (CM.add res c Unconsumed) lin
                  else CM.remove res c

let usedhere (rule : string) (res:consumed CM.t) (c:cvar) (frs:astinfo list) : consumed CM.t =
  match safefind rule res c with
  | Unconsumed -> errr (fst c) (rule^": Unconsumed but used channel "^string_of_cvar c)
  | Consumed -> res
  | Slack -> if is_aff c
             then List.iter frs (fun x -> x.affineFrees := CS.add !(x.affineFrees) c);
             CM.add res c Consumed

let un2coned (lin:sesenv) (must:CS.t) = CS.diff (keyset lin) must

(* TODO Get rid of this *)
(* To make the code and theoretical presentation match more closely, we have a subkind
   relation. Without ad-hoc polymorphism, I think this is as clean as it can get. Perhaps
   projecting to a new datatype would be better?
   Recall: Int < Aff < Lin  *)

let subkindVV v1 v2 = is_lin v2 || (is_aff v2 && not (is_lin v1)) || (is_shr v1 && is_shr v2)
let subkindVM v m = match m with 
                    | Linear -> true
                    | Affine -> is_aff v || is_shr v
                    | Intuist -> is_shr v

(* A test for whether synthM would (immediately?) fail. Might need to think about this
   a bit *)
let rec synthable e =
  match e with 
  | Var _ -> true
  | Con _ -> true
  | Bin _ -> true
  | Cast _ -> true
  | App _ -> true
  | Let (_,_,_,_,e2) -> synthable e2
  | _ -> false

(* Limited compatibility check used to ensure that we can downgrade an affine resource to
   linear transparently *)
let modeCompatable (m1:modality) (m2:modality) : bool =
  m1 = m2 || (m1 = Linear && m2 = Affine)

(* Check that a type is well formed wrt a set of mtype variables and session type
   variables. Should this be in destypes.ml? *)
(* TODO better error locations *)
let rec wfM_ (vs:stype list) (loc:srcloc) (wfms: SS.t) (wfss: TS.t) (tin:mtype) : unit =
  match !(getMType tin) with
  | MInd _ -> errr loc "BUG wfM_ MInd"
  | MVar -> errr loc "BUG wfM_ MVar"
  | MVarU x -> if not (SS.mem wfms x) then errr loc (x^" is not in scope")
  | MonT (Some s,args) -> wfS_ vs loc wfms wfss s; List.iter args (wfS_ vs loc wfms wfss)
  | MonT (None,args) -> List.iter args (wfS_ vs loc wfms wfss)
  | Comp (_,args) -> List.iter args (function
                                    | `M m -> wfM_ vs loc wfms wfss m
                                    | `S s -> wfS_ vs loc wfms wfss s)
and wfS_ (vs:stype list) (loc:srcloc) (wfms: SS.t) (wfss: TS.t) (tin:stype) : unit =
  if memq tin vs then () else
  let go (mode:modality) (s:stype) : unit =
    errr loc ("Expected a "^string_of_mode mode^" version of "^string_of_stype s
             ^" but found "^string_of_mode (getMode s)^" instead")
  in match !(getSType tin) with
  | SVar -> errr loc "BUG wfS SVar"
  | SInd _ -> errr loc "BUG wfS SInd"
  | SComp _ -> errr loc "BUG wfS SComp"
  | SVarU x -> if not (TS.mem wfss x) then errr loc (string_of_tyvar x^" is not in scope")
  | Stop _ -> ()
  | InD (mode,m,s) -> if not (mode = getMode s) 
                      then go mode s 
                      else wfM_ (tin::vs) loc wfms wfss m; wfS_ (tin::vs) loc wfms wfss s
  | OutD (mode,m,s) -> if not (mode = getMode s) 
                       then go mode s 
                       else wfM_ (tin::vs) loc wfms wfss m; wfS_ (tin::vs) loc wfms wfss s
  | InC (mode,s1,s2) -> if not (mode = getMode s1) then go mode s1;
                        if not (mode = getMode s2) then go mode s2;
                        wfS_ (tin::vs) loc wfms wfss s1; wfS_ (tin::vs) loc wfms wfss s2
  | OutC (mode,s1,s2) -> if not (mode = getMode s1) then go mode s1;
                         if not (mode = getMode s2) then go mode s2;
                         wfS_ (tin::vs) loc wfms wfss s1; wfS_ (tin::vs) loc wfms wfss s2
  | Intern (mode,lm) -> LM.iter lm (fun ~key:l ~data:s -> if not (mode = getMode s)
                                                          then go mode s
                                                          else wfS_ (tin::vs) loc wfms wfss s)
  | Extern (mode,lm) -> LM.iter lm (fun ~key:l ~data:s -> if not (mode = getMode s)
                                                          then go mode s
                                                          else wfS_ (tin::vs) loc wfms wfss s)
  | Forall (mode,x,s) -> if not (mode = getMode s) then go mode s;
                         wfS_ (tin::vs) loc wfms (TS.add wfss x) s
  | Exists (mode,x,s) -> if not (mode = getMode s) then go mode s;
                         wfS_ (tin::vs) loc wfms (TS.add wfss x) s
  | ShftUp (mode,s) -> if not (mode > getMode s)
                       then errr loc ("Tried to upcast from "^string_of_mode (getMode s)
                                     ^" to "^string_of_mode mode)
  | ShftDw (mode,s) -> if not (mode < getMode s)
                       then errr loc ("Tried to upcast from "^string_of_mode (getMode s)
                                     ^" to "^string_of_mode mode)

let wfM (loc:srcloc) (wfms: SS.t) (wfss: TS.t) (tin:mtype) : unit = wfM_ [] loc wfms wfss tin
let wfS (loc:srcloc) (wfms: SS.t) (wfss: TS.t) (tin:stype) : unit = wfS_ [] loc wfms wfss tin
        

(* We use unit since, we won't branch on failure, merely return an error to the user *)
(* We should use a specialized subtype at some point, the general one probably isn't so
safe *)
let rec subsumeM (rule:string) (wfms: SS.t) (wfss: TS.t) (env:funenv) (e:exp) (t:mtype) =
  prettyUnifM rule (locE e) (synthM wfms wfss env e) t

(* TODO `M case should just convert to the `P case and call that *)
and letcommon (sloc:srcloc) (wfms: SS.t) (wfss: TS.t) (env:funenv) 
              (tin:[`M of Fullsyntax.mtype | `P of Fullsyntax.ptype])
              (x:fvar) (e:exp) : ptype =
    match tin with
    | `M t -> 
      let mvs = SS.fold (Fullsyntax.freeMVarsMPure t) ~init:[] ~f:(fun acc x -> `M x :: acc)
      and svs = TS.fold (Fullsyntax.freeSVarsMPure t) ~init:[] ~f:(fun acc x -> `S x :: acc)
      in letcommon sloc wfms wfss env (`P (Fullsyntax.Poly(mvs@svs,t))) x e
    | `P (Fullsyntax.Poly (qs,t)) ->
      let wfms' = List.fold qs ~init:wfms ~f:(fun acc x -> match x with
                                                           | `M v -> SS.add acc v
                                                           | `S _ -> acc)
      and wfss' = List.fold qs ~init:wfss ~f:(fun acc x -> match x with
                                                           | `S v -> TS.add acc v
                                                           | `M _ -> acc)
      and t' = puretoptrM t
      in wfM sloc wfms' wfss' t';
         checkM wfms' wfss' (FM.add env x (Poly(qs,t'))) e t';
         Poly(qs,t')

and varcommon (env:funenv) (x:fvar) : mtype =
  if FM.mem env x
  then match (FM.find_exn env x) with
       | Poly (qs,t) -> 
         substM t (List.fold qs ~init:SM.empty
                  ~f:(fun acc q -> match q with
                  | `M v -> SM.add acc v (mkvar ())
                  | `S _ -> errr (fst x) (string_of_fvar x^" has session polymorphism in its type " 
                                         ^string_of_ptype (Poly(qs,t)) ^" Use "
                                         ^string_of_fvar x^"<...> instead")))
                TM.empty
  else if SM.mem !conTypes (snd x)
       then let argts,t = conInstance (snd x)
            in List.fold_right argts ~init:t ~f:(fun xt et -> mkfun xt et)
       else (match snd x with
            | "assert" -> mkfun booltype unittype
            | "sleep" -> mkfun inttype unittype
            | "print" -> mkfun inttype unittype
            | "print_str" -> mkfun stringtype unittype
            | "flush" -> mkfun unittype unittype
            | "i2s" -> mkfun inttype stringtype
            | "sexp2s" -> let a = mkvar () in mkfun a stringtype
            | "newkey" -> mkfun unittype (mkcomp "," [`M (mkcomp "Key" []);`M (mkcomp "Key" [])])
            | "encrypt" -> let a = mkvar () in 
              mkfun (mkcomp "Key" []) (mkfun a (mkcomp "<>" [`M a]))
            | "decrypt" -> let a = mkvar () in 
              mkfun (mkcomp "Key" []) (mkfun (mkcomp "<>" [`M a]) a)
            | "aesenc" -> let a = mkvar () in
              (mkfun a (mkfun (mkcomp "AESKey" []) stringtype))
            | "aesdec" -> let a = mkvar () in
              mkfun stringtype (mkfun (mkcomp "AESKey" []) a)
            | "aeskey" -> mkfun unittype (mkcomp "AESKey" [])
            | _ -> errr (fst x) ("Variable "^string_of_fvar x^" not found"))
  

and checkM (wfms: SS.t) (wfss: TS.t) (env:funenv) (ein:exp) (tin:mtype) : unit =
  if !infer_trace_flag
  then print_endline (loc2str (locE ein)^" checkM :: "^string_of_mtype tin);
   match ein with
   | Var (_,x) -> prettyUnifM "var" (fst x) (varcommon env x) tin
   | Con _ -> subsumeM "con" wfms wfss env ein tin
   | Bin (_,b,e1,e2) -> subsumeM "bin" wfms wfss env ein tin
   | Mon _ -> failwith "BUG checkM MonExp"
   | Sat (_,c,args) ->
     let argts,t = conInstance c
     in prettyUnifM "ADT" (locE ein) t tin;
        if not (List.length args = List.length argts)
        then errr (locE ein) ("Wrong number of arguments to "^c^" expected "
                             ^string_of_int (List.length argts)^" got "
                             ^string_of_int (List.length args))
        else List.iter2_exn args argts (checkM wfms wfss env)
   | Fun (_,x,e) ->
     let a,b = mkvar(),mkvar()
     in prettyUnifM "fun" (locE ein) (mkfun a b) (tin);
        checkM wfms wfss (FM.add env x (Poly ([],a))) e b
   | App _ -> subsumeM "app" wfms wfss env ein tin
   | Let (_,t,x,e1,e2) ->
       checkM wfms wfss (FM.add env x (letcommon (locE ein) wfms wfss env t x e1)) e2 tin
   | Cas (_,eb,es) ->
     let et = synthM wfms wfss env eb
     in SM.iter es (fun ~key:c ~data:(vs,e) ->
                   let argts,t = conInstance c
                   in prettyUnifM "case" (locE eb) t et;
                      checkM wfms wfss (List.fold2_exn vs argts ~init:env
                             ~f:(fun m x xt -> FM.add m x (Poly([],xt)))) e tin)
   | Monad (_,Some c,p,cs,_) -> (* TODO More tests where providing shared service *)
     (match !(getMType tin) with
     | MonT (Some t,ts) -> 
        if not (var2mode c = getMode t)
        then errr (fst c) ("Modality problem "^string_of_cvar c
                          ^" type is "^string_of_mode (getMode t)
                          ^" but channel is "^string_of_mode (var2mode c));
        List.iter cs (fun k -> if var2mode k < var2mode c then errr (fst k)
                           ("Modality problem "^string_of_cvar k));
        let senv : sesenv = 
                   match List.zip cs ts with
                   | Some x -> CM.of_alist_exn x
                   | None -> errr (fst c) ("Wrong number of argument channels. Expected "
                                          ^string_of_int (List.length ts)^" got "
                                          ^string_of_int (List.length cs))
        in let sub = checkS wfms wfss env senv p c t
           in allconsumed "monad" sub
     | _ -> errr (locE ein) ("Expected monad type found "^string_of_mtype tin))
   | Monad (_,None,p,cs,_) -> (* Copy/pasted from above. Sorry *)
     (match !(getMType tin) with
     | MonT (None,ts) -> 
        let senv : sesenv = 
                   match List.zip cs ts with
                   | Some x -> CM.of_alist_exn x
                   | None -> errr (locE ein) ("Wrong number of arguments. Expected "
                                          ^string_of_int (List.length ts)^" got "
                                          ^string_of_int (List.length cs))
        (* TODO is Linear correct? *)
        in let sub = checkS wfms wfss env senv p ((locE ein),Lin (priv_name ())) (mkstop Linear)
           in allconsumed "monad" sub
     | _ -> errr (locE ein) ("Expected detached monad type found "^string_of_mtype tin))
     | Cast (i,e,t) ->
         let t_ref = puretoptrM t
         and et    = synthM wfms wfss env e
         in wfM (locE ein) wfms wfss t_ref;
            (* Might as well do this, this unification might be unneeded *)
            prettyUnifM "Cast" (locE ein) t_ref tin;
            (match !(getMType et),!(getMType t_ref) with
            | MonT(Some s1,ss1),MonT(Some s2,ss2) -> (* TODO do we still want this? *)
              if not (List.length ss1 = List.length ss2)
              then failwith ("SubtypeM: mismatched monadic argument length");
              prettySubS "cast1" (locE ein) s1 s2;
              List.iter2_exn ss1 ss2 
                             (fun x y -> prettySubS "cast2" (locE ein) y x)
            | _,MonT _ -> errr (locE e) ("Expected: "^string_of_mtype t_ref^" found "^string_of_mtype et)
            | _,_ -> errr (locE ein) ("Coercions must be to a monadic type"))
   | Box _ -> failwith "checkM Box"
   | PolyApp _ -> subsumeM "polyapp" wfms wfss env ein tin

and synthM (wfms: SS.t) (wfss: TS.t) (env:funenv) (ein:exp) : mtype =
  let m = synthM_raw wfms wfss env ein
  in if !infer_trace_flag
     then print_endline (loc2str (locE ein)^" synthM : "^string_of_mtype m);
          m

and synthM_raw (wfms: SS.t) (wfss: TS.t) (env:funenv) (ein:exp) : mtype =
   match ein with
   | PolyApp (_,x,ss) -> 
     if FM.mem env x
     then match (FM.find_exn env x) with
          | Poly (qs,t) -> 
            if not ((List.length qs) = (List.length ss))
            then errr (locE ein) (string_of_fvar x ^ " has "^string_of_int (List.length qs)
                                 ^" quantifier(s) in its type "^string_of_ptype (FM.find_exn env x)
                                 ^" but "^string_of_int (List.length ss)^" type(s) were supplied");

            let subM,subS = List.fold2_exn qs ss ~init:(SM.empty,TM.empty)
              ~f:(fun (accm,accs) q amb ->
                 match q,amb with
                 | `S x,`S s -> let s' = puretoptrS s
                                in wfS (locE ein) wfms wfss s'; (accm,TM.add accs x s')
                 | `M x,`M m -> let m' = (puretoptrM m)
                                in wfM (locE ein) wfms wfss m'; (SM.add accm x m',accs)
                 | `S _,`M m -> errr (locE ein) ("tried to instantiate session type variable"
                                                ^" with data type "^Fullsyntax.string_of_mtype m)
                 | `M _,`S s -> errr (locE ein) ("tried to instantiate data type variable"
                                                ^" with session type "^Fullsyntax.string_of_stype s)
                 )
            in substM t subM subS
     else errr (fst x) ("Unbound variable "^string_of_fvar x)
   | Var (_,x) -> varcommon env x
   | Con (_,c) -> 
     (match c with
     | Int _ -> inttype
     | Float _ -> floattype
     | String _ -> stringtype)
   | Bin (_,b,e1,e2) ->
     (match b with
     | Add | Mul | Sub | Div ->
       checkM wfms wfss env e1 inttype;
       checkM wfms wfss env e2 inttype;
       inttype
     | FAdd | FSub | FMul | FDiv | Exp ->
       checkM wfms wfss env e1 floattype;
       checkM wfms wfss env e2 floattype;
       floattype
     | Syntax.Core.Less ->
       checkM wfms wfss env e1 inttype;
       checkM wfms wfss env e2 inttype;
       booltype
     | Concat ->
       checkM wfms wfss env e1 stringtype;
       checkM wfms wfss env e2 stringtype;
       stringtype
     | Eq ->
       prettyUnifM "bin-eq" (locE ein) (synthM wfms wfss env e1) (synthM wfms wfss env e2);
       booltype)
   | Mon _ -> failwith "synthM MonExp"
   | Sat (i,c,args) -> 
     let argts,t = conInstance c
     in (if not (List.length args = List.length argts)
        then errr (locE ein) ("Wrong number of arguments to "^c^" expected "
                             ^string_of_int (List.length argts)^" got "
                             ^string_of_int (List.length args))
        else List.iter2_exn args argts (checkM wfms wfss env));
     t
   | Fun (_,x,e) ->
     errr (locE ein) "Tried to synthesize type of anonymous function"
   | App (_,e1,e2) ->
     let a,b = mkvar(),mkvar()
     in prettyUnifM "app" (locE e1) (synthM wfms wfss env e1) (mkfun a b);
        checkM wfms wfss env e2 a;
        b
   | Let (_,t,x,e1,e2) ->
     synthM wfms wfss (FM.add env x (letcommon (locE ein) wfms wfss env t x e1)) e2
   | Cas (_,eb,es) -> 
     let et  = synthM wfms wfss env eb
     and ret = mkvar ()
     in SM.iter es (fun ~key:c ~data:(vs,e) ->
                   let argts,t = conInstance c
                   in prettyUnifM "case" (locE eb) t et;
                      prettyUnifM "case" (locE e) ret
                        (synthM wfms wfss (List.fold2_exn vs argts ~init:env
                             ~f:(fun m x xt -> FM.add m x (Poly ([],xt)))) e));
        ret
   | Monad _ -> errr (locE ein) "Tried to synthesise type for monad"
   | Cast (_,e,t) -> (* Unsure if this should be an error. *)
     let t' = puretoptrM t
     in wfM (locE ein) wfms wfss t';
        checkM wfms wfss env e t';
        t'
   | Box _ -> failwith "synthM Box"
(* Returns a slackness map *)
and checkS (wfms: SS.t) (wfss: TS.t) (env:funenv) (senv:sesenv) 
           (pin:proc) (cpr:cvar) (tin:stype) : consumed CM.t =
  if !infer_trace_flag
  then print_endline (loc2str (locP pin)^" checkS "^string_of_cvar cpr^" :: "^string_of_stype tin);
  let slackmap = checkS_raw wfms wfss env senv pin cpr tin
  in (* Invariant: Slackness maps should never include unrestricted channels in their domain *)
     CM.iter slackmap (fun ~key:k ~data:_ -> if not (is_shr k) 
                                             then ()
                                             else errr (locP pin) 
                                                       ("BUG Found unrestricted channel "
                                                       ^string_of_cvar k
                                                       ^" in slackness map"));
     
     slackmap
  
and checkS_raw (wfms: SS.t) (wfss: TS.t) (env:funenv) (senv:sesenv) 
               (pin:proc) (cpr:cvar) (tin:stype) : consumed CM.t = 
  match pin with
  | TailBind (_,c,e,cs) -> 
    (* This is separate to enable desugaring to be type based *)
    (* Specifically, desugaring creates a large number of anonymous monads and tail binds
       them. This means that we can't synthesise their types. Instead we assert that they
       are the type we need. Ideally, the theoretical development has a lemma to justify
       that expressions can be checked any supertype of one of the minimal types. *)
   
    (* Confirm that we're tailbinding to the correct variable *)
    if not (cvar_eq c cpr)
    then errr (fst c) ("Tailbind of incorrect variable. Expected: "^string_of_cvar cpr
                      ^" Found: "^string_of_cvar c)

    (* Check for unsafe duplications, I have no clue why this throws a warning *)
    (match List.find_a_dup ~compare:(fun x y -> Pervasives.compare (snd x) (snd y))
                           (List.filter cs (fun x -> not (is_shr x))) with
    | Some x -> errr (fst x) ("Duplicate usage of channel "^string_of_cvar x)
    | None -> ());


    (* Actually check the monadic expression after guessing its type *)
    let et = mkmon (Some tin) (List.map cs (fun x -> safefind "tail-bind" senv x))
    in checkM wfms wfss env e et;
 
    (* Find the residual and mark the channels consumed here as consumed, ignoring
       persistent ones. This works similarly to the code for the full bind *)
    let res = findResidual senv
    in List.fold_left cs ~init:res
                      ~f:(fun acc x ->
                         if is_shr x then acc
                         else match safefind "Tailbind BUG" res x with
                              | Unconsumed | Slack -> CM.add acc x Consumed
                              | Consumed -> errr (fst x) ("Channel Duplication "
                                                         ^string_of_cvar x))

  | Bind (_,c,e,cs,p)  ->
    let mont = getMType (synthM wfms wfss env e) in
    (match !mont with
    | MonT (Some ct,cts) ->

      (* Check for wrong number of args *)
      if not (List.length cs = List.length cts)
      then errr (locP pin) ("Wrong number of arguments to bind expected "
                           ^string_of_int (List.length cts)^" got "
                           ^string_of_int (List.length cs));

      (* Check for unsafe duplications *)
      (match List.find_a_dup ~compare:(fun x y -> Pervasives.compare (snd x) (snd y))
                             (List.filter cs (fun x -> not (is_shr x))) with
      | Some x -> errr (fst x) ("Duplicate usage of channel "^string_of_cvar x)
      | None -> ());

      (* Check for modality errors *)
      if not (var2mode c = getMode ct)
      then errr (fst c) ("mismatched modality: found "
                        ^string_of_mode (getMode ct)
                        ^" expected "^string_of_mode (var2mode c));
      List.iter2_exn cs cts (fun v t -> if not (getMode t = var2mode v)
                                            then errr (fst v) ("mismatched modality: found "
                                                               ^string_of_mode (var2mode v)
                                                               ^" expected "^string_of_mode (getMode t)));

      (* Check for subtyping errors *)
      List.iter2_exn cs cts (fun x xt -> prettySubS "{ }E" (fst x) (safefind "{ }E" senv x) xt);

      (* Get residual for subprocess:
         If a channel was consumed by this residual and also used as an argument,
         duplication of resources has occurred. *)
      let sub = boundhere "{ }E" senv (checkS wfms wfss env (CM.add senv c ct) p cpr tin) c [getinfoP p]
      in List.fold_left cs ~init:sub
                           ~f:(fun acc x ->
                            if is_shr x then acc (* unrestricted chans can't be in resid *)
                            else match safefind "{ }E BUG" sub x with
                                 | Unconsumed | Slack -> CM.add acc x Consumed
                                 | Consumed -> errr (fst x) ("Duplication of channel "
                                                                       ^string_of_cvar x))
    | MonT (None,cts) ->

      (* Check for wrong number of args *)
      if not (List.length cs = List.length cts)
      then errr (locP pin) ("Wrong number of arguments to bind expected "
                           ^string_of_int (List.length cts)^" got "
                           ^string_of_int (List.length cs));

      (* Check for unsafe duplications *)
      (match List.find_a_dup ~compare:(fun x y -> Pervasives.compare (snd x) (snd y))
                             (List.filter cs (fun x -> not (is_shr x))) with
      | Some x -> errr (fst x) ("Duplicate usage of channel "^string_of_cvar x)
      | None -> ());

      (* Check for modality errors *)
      List.iter2_exn cs cts (fun v t -> if not (getMode t = var2mode v)
                                            then errr (fst v) ("mismatched modality: found "
                                                               ^string_of_mode (var2mode v)
                                                               ^" expected "^string_of_mode (getMode t)));

      (* Check for subtyping errors *)
      List.iter2_exn cs cts (fun x xt -> prettySubS "{ }E_2" (fst x) (safefind "{ }E_1" senv x) xt);

      (* Get residual for subprocess:
         If a channel was consumed by this residual and also used as an argument,
         duplication of resources has occurred. *)
      let sub = checkS wfms wfss env senv p cpr tin
      in List.fold_left cs ~init:sub
                           ~f:(fun acc x ->
                            if is_shr x then acc (* unrestricted chans can't be in resid *)
                            else match safefind "{ }E_ BUG" sub x with
                                 | Unconsumed | Slack -> CM.add acc x Consumed
                                 | Consumed -> errr (fst x) ("Duplication of channel "
                                                                       ^string_of_cvar x))
    | _ -> errr (locE e) ("Bind of non monad type: "^string_of_mtype mont))
  | Service (i,c,s,p) ->
    if cvar_eq c cpr
    then errr (ast2loc i) "Bound service to yourself?!"
    else let sub = checkS wfms wfss env (CM.add senv c 
                                      (match FM.find !sessions s with
                                      | None -> errr (fst s) ("Unknown session name: " 
                                                             ^string_of_fvar s)
                                      | Some t -> t))
                                  p cpr tin
         in boundhere "service" senv sub c [getinfoP p]
  | Register (i,s,c,p) ->
    if cvar_eq c cpr
    then errr (ast2loc i) "Registered yourself?!"
    else prettySubS "register" (fst c) (safefind "register" senv c)
                                        (match FM.find !sessions s with
                                        | None -> errr (fst s) ("Unknown session name: "
                                                               ^string_of_fvar s)
                                        | Some t -> t);
         CM.add (checkS wfms wfss env (CM.remove senv c) p cpr tin) c Consumed
  | InputD (i,x,c,p)  ->
    if cvar_eq c cpr
    then (match !(getSType tin) with
         | InD (_,et,pt) ->
           checkS wfms wfss (FM.add env x (Poly([],et))) senv p cpr pt
         | _ -> errr (fst c) ("=>R expected "^string_of_cvar cpr^" to have => type.  Found "
                               ^string_of_stype tin))
    else (match !(getSType (safefind "/\\L" senv c)) with
         | OutD (_,xt,ct) -> 
           usedhere "/\\L" (checkS wfms wfss (FM.add env x (Poly([],xt))) (CM.add senv c ct) p cpr tin) c [getinfoP p]
         | _ -> errr (fst c) ("/\\L expected "^string_of_cvar cpr^" to have /\\ type.  Found "
                               ^string_of_stype (safefind "/\\L" senv c)))
  | OutputD (i,c,e,p)  ->
    if cvar_eq c cpr
    then (match !(getSType tin) with
         | OutD (_,et,pt) ->
           checkM wfms wfss env e et;
           checkS wfms wfss env senv p cpr pt
         | _ -> errr (fst cpr) ("/\\R expected "^string_of_cvar cpr^" to have /\\ type.  Found "
                               ^string_of_stype tin))
    else (match !(getSType (safefind "=>L" senv c)) with
         | InD (_,et,ct) -> 
           checkM wfms wfss env e et;
           usedhere "=>L" (checkS wfms wfss env (CM.add senv c ct) p cpr tin) c [getinfoP p]
         | _ -> errr (fst c) ("=>L expected "^string_of_cvar c^" to have => type.  Found "
                               ^string_of_stype (safefind "=>L" senv c)))
  | InputC (i,ambigref,c1,c2,p) ->
    if cvar_eq c2 cpr
    then match !(getSType tin) with
         | InC (m,c1t,pt) -> 
           if not (!ambigref = `Tensor)
           then errr (locP pin) ("-oR: Type of "^string_of_cvar c2^" is "^string_of_stype tin
                                ^" but "^string_of_cvar c1^" isn't the same modality");

           if not (var2mode c1 = m) then errr (fst c1)
              "-oR: modality mismatch";
           let sub = checkS wfms wfss env (CM.add senv c1 c1t) p cpr pt
           in boundhere "-oR/UpR" senv sub c1 [getinfoP p]
         | ShftUp (_,t) -> 
           (* We need to:
              1) confirm that c1 is a lower mode than c2? Paper has this implicit in the syntax. 
              2) Confirm that c2 is the channel we're supposed to be providing.
              3) Deconstruct the provided type to get the continuation type
              4) Change the provided channel to new one (i.e., swap c1 with c2).
              5) The residual should be the same as that for the continuation since the newly
                 "bound" variable doesn't show up in the environment.
           *)
     
           (* check condition 1 *)
           if not (var2mode c1 < var2mode c2)
           then errr (fst c1) ("UpR: mode of "^string_of_cvar c2^" should be lower than that of "
                              ^string_of_cvar c1);

           (* Might not be needed, but confirm that our earlier disambiguation agrees here *)
           if not (!ambigref = `UpCastR)
           then errr (locP pin) ("UpcastR: Type of "^string_of_cvar c2^" is "^string_of_stype tin
                                ^" but "^string_of_cvar c1^" isn't a legal modality");
     
           (* check condition 2 *)
           if not (cvar_eq c2 cpr)
           then errr (fst c2) ("UpR must receive on provided channel: expected "
                              ^string_of_cvar cpr^" found "^string_of_cvar c2);

           (* get the continuation residual *)
           checkS wfms wfss env senv p c1 t
         | _ -> errr (ast2loc i) ("-oR/UpR: Expected -o/Up found "^string_of_stype tin)
    else (match !(getSType (safefind "*L/DowncastL" senv c2)) with
         | OutC (m,c1t,c2t) -> 
           (* Might not be needed, but confirm that our earlier disambiguation agrees here *)
           if not (!ambigref = `Tensor)
           then errr (locP pin) ("*L: Type of "^string_of_cvar c2^" is "^string_of_stype tin
                                ^" but "^string_of_cvar c1^" isn't a legal modality");

           (* TODO Remove this subkinding *)
           if not (subkindVV c1 cpr) then errr (fst c1)
              ("Trying to bind linear channel "^string_of_cvar c1^" while providing an affine service");
           if not (var2mode c1 = m) then errr (fst c1)
              ("*L modality mismatch");
           let sub = checkS wfms wfss env (CM.add (CM.add senv c2 c2t) c1 c1t) p cpr tin
           in boundhere "*L" senv (usedhere "*L" sub c2 [getinfoP p]) c1 [getinfoP p]
         | ShftDw (_,t) ->
           (* Might not be needed, but confirm that our earlier disambiguation agrees here *)
           if not (!ambigref = `DwCastL)
           then errr (locP pin) ("DowncastL: Type of "^string_of_cvar c2^" is "^string_of_stype tin
                                ^" but "^string_of_cvar c1^" isn't a legal modality");
           (* Note this case is disambiguated from other channel reception via types
              We need to do/check:
              1) c1 isn't the provided channel
              2) c2 isn't the provided channel
              3) remove c2 and add c1 at the correct type
              4) residual of p needs to treat c1 as newly bound
              5) returned residual treats c2 as consumed
           *) (* TODO do we need more mode checks? *)

           (* Check condition 1 *)
           if cvar_eq c1 cpr
           then errr (fst c1) ("DowncastL: "^string_of_cvar c1^" cannot be the provided channel "
                              ^string_of_cvar cpr);

           (* Check condition 2 *)
           if cvar_eq c2 cpr
           then errr (fst c2) ("DowncastL: "^string_of_cvar c2^" cannot be the provided channel "
                              ^string_of_cvar cpr);

           (* Get continuation residual *)
           let r = checkS wfms wfss env (CM.add (CM.remove senv c2) c1 t) p cpr tin
           in let r' = boundhere "DowncastL" (CM.remove senv c2) r c1 [getinfoP p]
              in CM.add r' c2 Consumed

         | _ -> errr (fst c2) ("*L/DowncastL: expected */DowncastL found "
                              ^string_of_stype (safefind "*L/DowncastL" senv c2)))
  | OutputC (i,c,d,pd,p) ->
    if cvar_eq c cpr
    then match !(getSType tin) with
         | OutC (m,dt,pt) ->
            (* Make sure the type mode is compatible with the new proc *)
            if not (var2mode d = m) then errr (fst d) "*R modality mismatch";
            let resd =  (* Ensure that affine contexts don't use linear channels. *)
                       CM.mapi (checkS wfms wfss env senv pd d dt)
                              ~f:(fun ~key:k ~data:rd ->
                                      match rd with
                                      | Consumed -> if not (subkindVV k d)
                                                    then errr (fst k) "linear channel in affine context"
                                                    else Consumed
                                      | Unconsumed -> Unconsumed
                                      | Slack -> if not (subkindVV k d) then Unconsumed else Slack)
            and resp = checkS wfms wfss env senv p cpr pt
            in samekeys (locP pin) "*R" resd resp;
               CM.mapi resp ~f:(fun ~key:k ~data:rp ->
                       match safefind "*R" resd k, rp with
                       | Consumed, Consumed -> errr (locP pin) ("Duplicate usage of channel "
                                                               ^string_of_cvar k)
                       | Consumed,_ -> Consumed
                       | _,Consumed -> Consumed
                       | Slack,_ -> Slack
                       | _,Slack -> Slack
                       | Unconsumed,Unconsumed -> Unconsumed)
        | _ -> errr (ast2loc i) ("*R: expected * found "^string_of_stype tin)
    else (match !(getSType (safefind "-oL" senv c)) with
         | InC (m,dt,ct) ->
            if not (var2mode d = m) then errr (fst d) "-oL modality mismatch";
            let resd = (* Ensure that affine contexts don't use linear channels. *)
                       (* TODO This probably shouldn't be copy/pasted from *R *)
                       CM.mapi (checkS wfms wfss env senv pd d dt)
                              ~f:(fun ~key:k ~data:rd ->
                                      match rd with
                                      | Consumed -> if not (subkindVV k d)
                                                    then errr (fst k) "linear channel in affine context"
                                                    else Consumed
                                      | Unconsumed -> Unconsumed
                                      | Slack -> if not (subkindVV k d) then Unconsumed else Slack)
            and resp = usedhere "-oL" (checkS wfms wfss env (CM.add senv c ct) p cpr tin) c [getinfoP p]
            in samekeys (locP pin) "-oL" resd resp;
               CM.mapi resp ~f:(fun ~key:k ~data:rp ->
                       match safefind "*R" resd k, rp with
                       | Consumed, Consumed -> errr (locP pin) ("Duplicate usage of channel "
                                                               ^string_of_cvar k)
                       | Consumed,_ -> Consumed
                       | _,Consumed -> Consumed
                       | Slack,_ -> Slack
                       | _,Slack -> Slack
                       | Unconsumed,Unconsumed -> Unconsumed)
         | _ -> errr (fst d) ("-oL: expected -o found "^string_of_stype (safefind "-oL" senv c)))
  | Close (_,c)  ->
    (* Confirm we're closing the provided channel *)
    if not (cvar_eq c cpr)
    then errr (fst c) ("Tried to close "^string_of_cvar c^" when providing "^string_of_cvar cpr);
    
    (* TODO confirm that modes have already been checked *)
    (match !(getSType tin) with
    | Stop _ -> findResidual senv
    | _ -> errr (fst c) ("1R expected "^string_of_cvar c^" to have type 1. Found "
                        ^string_of_stype tin))
  | Exit _ -> 
    (prettyUnifS "Exit BUG" (locP pin) tin (mkstop Linear);
          findResidual senv)
  | Wait (_,c,p) ->
    if cvar_eq c cpr
    then errr (fst c) ("Waiting on itself while providing "^string_of_cvar c)
    else prettyUnifS "1L" (fst c) (mkstop Linear) (safefind "1L" senv c); (* TODO Mode sensitivity *)
         CM.change (checkS wfms wfss env (CM.remove senv c) p cpr tin) c (fun _ -> Some Consumed)
  | Fwd (_,c,d) ->
    if cvar_eq c cpr
    then if modeCompatable (var2mode c) (var2mode d)
         then
            ((prettySubS "id" (fst d) (safefind "id" senv d) tin;
            CM.add(findResidual (CM.remove senv d))) d Consumed)
         else errr (fst c) "fwd: mismatched modality"
    else errr (fst c) ("Forward to wrong channel wanted "^string_of_cvar cpr
                       ^" got "^string_of_cvar c)
  | External (_,c,ps) ->
    if cvar_eq c cpr
    then match !(getSType tin) with
      | Extern (_,ts) -> (* TODO Mode *)
        (* First find the residuals for each possible subprocess mentioned in the type *)
        let ress = LM.mapi ts (fun ~key:l ~data:t -> match LM.find ps l with
                                    | None -> errr (locP pin) ("&R: Expected to find "^string_of_label l) 
                                    | Some p -> checkS wfms wfss env senv p cpr t)
        in

        (* As a sanity check ensure that all the channels in the environment are in the
           residuals. *)
        (match LM.iter ress (fun ~key:l ~data:r -> 
              samekeys (locP pin) ("&R-"^string_of_label l) r (CM.filter senv (fun ~key:x ~data:_ -> 
                                                                               not (is_shr x)))) with
        | _ -> ());

        (* Combine the residuals. To do this a channel needs to be Unconsumed if it is in
           any branch; Consumed if it is in any branch; and slack otherwise. This raises
           an error if there is a Consumed/Unconsumed conflict. Additionally, for affine
           channels that are converted from Slack to Consumed during this we need to
           ensure that they will be GC'ed on the Slack branches. *)
        let resmerged = 
          LM.fold ress ~init:(CM.filter_mapi senv ~f:(fun ~key:k ~data:_ -> if is_shr k
                                                                        then None 
                                                                        else Some Slack))
          ~f:(fun ~key:l ~data:resp resa ->
             CM.mapi resa ~f:(fun ~key:k ~data:ra ->
                match ra, CM.find_exn resp k with
                | Consumed, Consumed -> Consumed
                | Consumed, Slack -> Consumed
                | Slack, Consumed -> Consumed
                | Slack, Slack -> Slack
                | Slack, Unconsumed -> Unconsumed
                | Unconsumed, Slack -> Slack
                | Unconsumed, Unconsumed -> Unconsumed
                | Consumed, Unconsumed
                | Unconsumed, Consumed -> errr (locP (LM.find_exn ps l))
                                               ("&R: Mismatched consumed resources at label "
                                               ^string_of_label l
                                               ^" channel "^string_of_cvar k
                                               ^" was found to be "^string_of_consumed ra
                                               ^" previously but is "
                                               ^string_of_consumed (CM.find_exn resp k)
                                               ^" here.")))
        in 
        
        (* Insert GC instructions *)
        CM.iter resmerged (fun ~key:c ~data:r ->
             match snd c with
             | Shr _ | Lin _ -> ()
             | Aff _ -> (match r with (* Unconsumed would be a BUG here *)
                        | Slack -> ()
                        | Unconsumed -> errr (locP pin) "extern BUG"
                        | Consumed -> LM.iter ress (fun ~key:l ~data:res ->
                                         (match CM.find res c with
                                         | Some Unconsumed -> errr (locP pin) "extern BUG"
                                         | Some Slack -> 
                                           let csr = (getinfoP (LM.find_exn ps l)).affineFrees
                                           in csr := CS.add !csr c
                                         | Some Consumed -> ()
                                         | None -> errr (locP pin) "extern BUG"))));
         
        (* Return the merged residual *)
        resmerged
      | _ -> errr (locP pin) "Expected External choice for &R"
    else (match !(getSType (safefind "+L" senv c)) with
      (* TODO Combine the residual finding of these two *)
      | Intern (m,ts) -> (* TODO mode *)
        usedhere "+L" (
        (* First find the residuals for each possible subprocess mentioned in the type *)
        let ress = LM.mapi ts (fun ~key:l ~data:t -> match LM.find ps l with
                                    | None -> errr (locP pin) ("+L: Expected to find label "^string_of_label l) 
                                    | Some p -> checkS wfms wfss env (CM.add senv c t) p cpr tin)
        in

        (* As a sanity check ensure that all the channels in the environment are in the
           residuals. *)
        (match LM.iter ress (fun ~key:l ~data:r -> 
              samekeys (locP pin) ("+L-"^string_of_label l) r (CM.filter senv (fun ~key:x ~data:_ -> 
                                                                               not (is_shr x)))) with
        | _ -> ());

        (* Combine the residuals. To do this a channel needs to be Unconsumed if it is in
           any branch; Consumed if it is in any branch; and slack otherwise. This raises
           an error if there is a Consumed/Unconsumed conflict. Additionally, for affine
           channels that are converted from Slack to Consumed during this we need to
           ensure that they will be GC'ed on the Slack branches. *)
        let resmerged = 
          LM.fold ress ~init:(CM.filter_mapi senv ~f:(fun ~key:k ~data:_ -> if is_shr k
                                                                        then None 
                                                                        else Some Slack))
          ~f:(fun ~key:l ~data:resp resa ->
             CM.mapi resa ~f:(fun ~key:k ~data:ra ->
                match ra, CM.find_exn resp k with
                | Consumed, Consumed -> Consumed
                | Consumed, Slack -> Consumed
                | Slack, Consumed -> Consumed
                | Slack, Slack -> Slack
                | Slack, Unconsumed -> Unconsumed
                | Unconsumed, Slack -> Slack
                | Unconsumed, Unconsumed -> Unconsumed
                | Consumed, Unconsumed
                | Unconsumed, Consumed -> errr (locP (LM.find_exn ps l))
                                               ("+L: Mismatched consumed resources at label "
                                               ^string_of_label l
                                               ^" channel "^string_of_cvar k
                                               ^" was found to be "^string_of_consumed ra
                                               ^" previously but is "
                                               ^string_of_consumed (CM.find_exn resp k)
                                               ^" here.")))
        in 
        
        (* Insert GC instructions *)
        CM.iter resmerged (fun ~key:c ~data:r ->
             match snd c with
             | Shr _ | Lin _ -> ()
             | Aff _ -> (match r with (* Unconsumed would be a BUG here *)
                        | Slack -> ()
                        | Unconsumed -> errr (locP pin) "extern BUG"
                        | Consumed -> LM.iter ress (fun ~key:l ~data:res ->
                                         (match CM.find res c with
                                         | Some Unconsumed -> errr (locP pin) "extern BUG"
                                         | Some Slack -> 
                                           let csr = (getinfoP (LM.find_exn ps l)).affineFrees
                                           in csr := CS.add !csr c
                                         | Some Consumed -> ()
                                         | None -> errr (locP pin) "extern BUG"))));
         
        (* Return the merged residual *)
        resmerged
             ) c []
      | _ -> errr (fst c) ("Expected Internal choice for +L found "
                          ^string_of_stype (safefind "+L" senv c)))
  | Internal (_,c,l,p) ->
    if cvar_eq c cpr
    then match !(getSType tin) with
         | Intern (_,ts) -> if LM.mem ts l
                        then checkS wfms wfss env senv p cpr (LM.find_exn ts l)
                        else errr (fst l) ("label "^string_of_label l^" not in expected type "
                                            ^string_of_stype tin)
         | _ -> errr (locP pin) "Non internal choice while checking +R"
    else (match !(getSType (safefind "&L" senv c)) with
         | Extern (_,ts) -> if LM.mem ts l
                        then usedhere "&L" (checkS wfms wfss env (CM.add senv c (LM.find_exn ts l)) 
                                                   p cpr tin) c [getinfoP p]
                        else errr (fst l) ("label "^string_of_label l^" not in expected type "
                                          ^string_of_stype (CM.find_exn senv c))
         | _ -> errr (locP p) "Non external choice while checking &L")
  | InputTy (_,x,c,p) -> 
    if cvar_eq c cpr
    then (match !(getSType tin) with
         | Forall (_,xt,pt) ->
           checkS wfms wfss env senv p cpr pt
         | _ -> errr (locP pin) ("forallR: expected forall type but found "^string_of_stype tin))
    else (match !(getSType (safefind "existsL" senv c)) with
         | Exists (_,xt,ct) -> 
           checkS wfms wfss env (CM.add senv c ct) p cpr tin
         | _ -> errr (fst c) ("Expected exists type. Found: "^string_of_stype (safefind "existsL" senv c)))
  | OutputTy (_,c,st,p) ->
    let st' = puretoptrS st
    in wfS (locP pin) wfms wfss st';
    if cvar_eq c cpr
    then (match !(getSType tin) with
         | Exists (_,x,ct) -> 
           checkS wfms wfss env senv p cpr (substS ct (SM.empty)
                                                   (TM.singleton x st'))
         | _ -> errr (fst c) ("Expected exists type. Found: "^string_of_stype tin))
    else (* Should this have an occurs check? *)
         (match !(getSType (safefind "forallL" senv c)) with
         | Forall (_,x,ct) ->
          usedhere "forallL" (checkS wfms wfss env (CM.add senv c (substS ct (SM.empty) (TM.singleton x st'))) p cpr tin) c
                     [getinfoP p]
         | _ -> errr (fst c) ("Expected forall type. Found: "^string_of_stype (safefind "forallL" senv c)))
  | ShftUpL (_,c1,c2,p) -> 
     (* We need to do/check:
        1) c1 is a lower mode than c2? Paper has this implicit in the syntax. 
        2) c2 isn't the channel we're supposed to be providing
        3) c1 is at least the mode of the channel we're providing
        4) remove c2 and add c1 to the environment
        5) residual from p needs to treat c1 as a bound variable
        6) residual returned consumes c2 (TODO What about unrestricted case?)

        If the channel is unrestricted don't remove it
     *) 

     (* check condition 1 *)
     if not (var2mode c1 < var2mode c2)
     then errr (fst c1) ("UpL: mode of "^string_of_cvar c1^" should be lower than that of "
                        ^string_of_cvar c2);

     (* check condition 2 *)
     if cvar_eq c2 cpr
     then errr (fst c2) ("UpL: cannot receive on the channel the current process is providing: "
                        ^string_of_cvar cpr);

     (* check condition 3 *)
     if not (var2mode c1 >= var2mode cpr)
     then errr (fst c1) ("UpL: Expected mode of "^string_of_cvar c1^" to be higher than that of "
                        ^string_of_cvar cpr);

     (* get the type for c1 *)
     (match !(getSType (safefind "UpL" senv c2)) with
     | SInd _ -> errr (locP pin) "BUG checkS-ShftUpL SInd after getSType"
     | ShftUp (Intuist,t) ->
       let r = checkS wfms wfss env (CM.add senv c1 t) p cpr tin
       in boundhere "UpL" senv r c1 [getinfoP p]
     | ShftUp (_,t) ->
       let r = checkS wfms wfss env (CM.add (CM.remove senv c2) c1 t) p cpr tin
       in let r' = boundhere "UpL" (CM.remove senv c2) r c1 [getinfoP p]
          in (* TODO does this need to confirm that c2 doesn't exist? *)
             CM.add r' c2 Consumed
     | _ -> errr (locP pin) ("UpL: Expected ShiftUp type. Found: "^string_of_stype tin))
     
  | ShftDwR (_,c1,c2,p) ->
     (* We need to do/check:
        1) c1 is the provided channel
        2) c2 is higher than c1 (paper does this syntactically)
        3) restrict the environment to only things higher modality than c2
        4) check p as providing c2 with the continuation type
        5) residual is that of p with the stuff excluded by step 4 marked unconsumed
     *)

     (* Check condition 1 *)
     if cvar_eq c2 cpr
     then errr (fst c2) ("DownR: cannot receive on the channel the current process is providing: "
                        ^string_of_cvar cpr);

     (* Check condition 2 *)
     if not (var2mode c2 >= var2mode c1)
     then errr (fst c2) ("DownR: Expected mode of "^string_of_cvar c2^" to be higher than that of "
                        ^string_of_cvar c1);

     (* Check condition 3. First component of the pair is things of higher modality. *)
     let high,low = CM.fold senv ~init:(CM.empty,CM.empty)
                       ~f:(fun ~key:c ~data:t (high,low) -> if var2mode c >= var2mode c2
                                                            then (CM.add high c t,low)
                                                            else (high,CM.add low c t))
     in (* Get continuation type *)
        (match !(getSType tin) with
        | SInd _ -> errr (locP pin) "BUG checkS-ShftDwR SInd after getSType"
        | ShftDw (_,t) -> 
          let r = checkS wfms wfss env senv p c2 t
          in (* Combine the residual with the stuff in low *)
             CM.merge (CM.map low (fun _ -> Unconsumed)) r 
               ~f:(fun ~key:c v -> match v with
                                   | `Both _ -> failwith "BUG ShftDwR merge"
                                   | `Left t' | `Right t' -> Some t')
        | _ -> errr (locP pin) ("DownR: Expected ShiftDw type. Found: "^string_of_stype tin))

let toplevel (ds:toplvl list) : unit=
  let _ = List.fold_left ds ~init:FM.empty
    ~f:(fun env d -> clearmaps ();
        match d with
        | TopLet (f,t,e) -> let p = letcommon (fst f) SS.empty TS.empty env t f e
                            in  FM.add env f p
        | TopProc (c,p) -> allconsumed "top" (checkS SS.empty TS.empty env CM.empty p c (mkstop Linear));
                           env
        | Pass -> env
        | ServDecl (f,s) -> sessions := FM.add !sessions f (Connection.puretoptrS s); env
        | MTypeDecl (t,fs,cm) -> SM.iter cm (fun ~key:c ~data:a -> 
            Types.Dest.conTypeNames := SM.add !Types.Dest.conTypeNames c (snd t);
            Types.Dest.conArities := SM.add !Types.Dest.conArities c (List.length a);
            Types.Dest.conTypes := SM.add !Types.Dest.conTypes c 
           (fs
           ,List.map a Connection.puretoptrM,ref(Comp(snd t,List.map fs (function 
                                                                        | `M x -> `M (ref (MVarU x))
                                                                        | `S s -> `S (ref (SVarU s)))))));
           env
        | STypeDecl (t,fs,s) -> 
          let s' = Connection.puretoptrS s
          in Connection.sessionDefs := SM.add !Connection.sessionDefs (snd t) (fs,s');
             env)
  in ()
