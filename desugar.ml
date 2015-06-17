open Base
open Core.Std
open Vars
open Syntax
open Types

let loc2ast l = { Syntax.Core.astloc = l; Syntax.Core.affineFrees = ref CS.empty; }

let rec desugarExp (ein:Full.exp) : Core.exp =
  match ein with
  | Full.Var (i,(_,"not")) -> 
    desugarExp (Full.Let (i,`M (Full.Comp(i,"->",[`M (Full.Comp(i,"Bool",[]))
                                                 ;`M (Full.Comp(i,"Bool",[]))]))
                           ,(i,"f")
                           ,[(i,"x")]
                           ,Full.If(i
                                   ,Full.Var(i,(i,"x"))
                                   ,Full.Sat(i,"False",[])
                                   ,Full.Sat(i,"True",[]))
                           ,Full.Var(i,(i,"f"))))
  | Full.Var (i,f) -> Core.Var (loc2ast i,f)
  | Full.Con (i,Full.Int x) -> Core.Con (loc2ast i,Core.Int x)
  | Full.Con (i,Full.Float x) -> Core.Con (loc2ast i,Core.Float x)
  | Full.Con (i,Full.String x) -> Core.Con (loc2ast i,Core.String x)
  | Full.Bin (i,b,e1,e2) -> 
    (match b with
    | Full.Add -> Core.Bin (loc2ast i,Core.Add,desugarExp e1,desugarExp e2)
    | Full.Sub -> Core.Bin (loc2ast i,Core.Sub,desugarExp e1,desugarExp e2)
    | Full.Mul -> Core.Bin (loc2ast i,Core.Mul,desugarExp e1,desugarExp e2)
    | Full.Div -> Core.Bin (loc2ast i,Core.Div,desugarExp e1,desugarExp e2)
    | Full.Exp -> Core.Bin (loc2ast i,Core.Exp,desugarExp e1,desugarExp e2)
    | Full.FAdd -> Core.Bin (loc2ast i,Core.FAdd,desugarExp e1,desugarExp e2)
    | Full.FSub -> Core.Bin (loc2ast i,Core.FSub,desugarExp e1,desugarExp e2)
    | Full.FMul -> Core.Bin (loc2ast i,Core.FMul,desugarExp e1,desugarExp e2)
    | Full.FDiv -> Core.Bin (loc2ast i,Core.FDiv,desugarExp e1,desugarExp e2)
    | Full.Concat -> Core.Bin (loc2ast i,Core.Concat,desugarExp e1,desugarExp e2)
    | Full.Eq -> Core.Bin (loc2ast i,Core.Eq,desugarExp e1,desugarExp e2)
    | Full.Less -> Core.Bin (loc2ast i,Core.Less,desugarExp e1,desugarExp e2)
    | Full.And -> desugarExp (Full.If(i,e1,e2,Full.Sat(i,"False",[])))
    | Full.Or -> desugarExp (Full.If(i,e1,Full.Sat(i,"True",[]),e2))
    | Full.GT -> desugarExp (Full.Bin(i,Full.Less,e2,e1))
    | Full.GE -> desugarExp (Full.Bin(i,Full.Or,(Full.Bin(i,Full.GT,e1,e2))
                                               ,(Full.Bin(i,Full.Eq,e1,e2))))
    | Full.LE -> desugarExp (Full.Bin(i,Full.Or,(Full.Bin(i,Full.Less,e1,e2))
                                               ,(Full.Bin(i,Full.Eq,e1,e2))))
  )
  | Full.If (i,eb,et,ef) ->
    desugarExp (Full.Case (i,eb
                          ,SM.of_alist_exn [("True",([],et));("False",([],ef))]))
  | Full.Case (i,e,br) -> 
    (* First Check a bunch of errors *)
    if SM.is_empty br then errr (Full.locE e) "empty case";
    Core.Cas (loc2ast i,desugarExp e,SM.map br (fun (pat,eb) -> (pat,desugarExp eb)))
  | Full.Sat (i,c,es) -> Core.Sat (loc2ast i,c,List.map es desugarExp)
  | Full.Fun (i,x,xs,e) -> 
    Core.Fun (loc2ast i,x,List.fold_right xs ~init:(desugarExp e)
                               ~f:(fun a ea -> Core.Fun (loc2ast i,a,ea)))
  | Full.App (i,e1,e2) -> Core.App (loc2ast i,desugarExp e1,desugarExp e2)
  | Full.Let (i,t,x,xs,e1,e2) -> 
    Core.Let (loc2ast i,t,x
             ,desugarExp (match xs with [] -> e1 | hd::tl -> Full.Fun(i,hd,tl,e1))
             ,desugarExp e2)
  | Full.Monad (i,Some c,p,cs) -> Core.Monad (loc2ast i,Some c,desugarProc c (CS.of_list cs) p,cs,None)
  | Full.Monad (i,None,p,cs) -> let tmpc = (i,Aff (priv_name ()))
                                in Core.Monad (loc2ast i,None,desugarProc tmpc (CS.of_list cs) p,cs,None)
  | Full.Cast (i,e,t) -> Core.Cast (loc2ast i,desugarExp e,t)
  | Full.Box (i,e,t) -> Core.Box (loc2ast i,desugarExp e,t)
  | Full.PolyApp (i,x,args) -> Core.PolyApp(loc2ast i,x,args)

(* Some of our desugaring requires knowledge of the currently provided channel and all
   those in scope. *)
and desugarProc (this:cvar) (scope:CS.t) (pin:Full.proc) : Core.proc =
  match pin with
  | Full.Detached (i,e,cs,p) -> let tmpc = (i,Aff (priv_name ()))
                              in Core.Bind (loc2ast i,tmpc,desugarExp e,cs
                                        ,desugarProc this (CS.add (CS.diff scope (CS.of_list cs)) tmpc) p)
  | Full.Bind (i,c,e,cs,p) -> Core.Bind (loc2ast i,c,desugarExp e,cs
                                        ,desugarProc this (CS.add (CS.diff scope (CS.of_list cs)) c) p)
  | Full.Service (i,c,n,p) -> Core.Service (loc2ast i,c,n,desugarProc this (CS.add scope c) p)
  | Full.Register (i,n,c,p) -> Core.Register (loc2ast i,n,c,desugarProc this (CS.remove scope c) p)
  | Full.InD (i,x,c,p) -> Core.InputD (loc2ast i,x,c,desugarProc this scope p)
  | Full.OutD (i,c,e,p) -> Core.OutputD (loc2ast i,c,desugarExp e,desugarProc this scope p)
  | Full.InC (i,cx,cc,p) -> 
    (match compare (var2mode cx) (var2mode cc) with
    | 0  -> Core.InputC (loc2ast i,ref `Tensor,cx,cc,desugarProc this (CS.add scope cx) p)
    | -1 -> Core.InputC (loc2ast i,ref `UpCastR,cx,cc,desugarProc cx scope p)
    | 1  -> Core.InputC (loc2ast i,ref `DwCastL,cx,cc,desugarProc this (CS.add (CS.remove scope cc) cx) p)
    | _  -> failwith "BUG compare doesn't work like I thought")
  | Full.OutC (i,cc,ct,pt,p) -> 
    Core.OutputC (loc2ast i,cc,ct,desugarProc ct (CS.inter scope (Full.freeCVars pt)) pt
                 ,desugarProc this (CS.inter scope (Full.freeCVars p)) p)
  | Full.Throw (i,cc,ct,p) ->
    let tmp = (fst ct,Lin ("throw_"^priv_name ()))
    in desugarProc this scope (Full.OutC (i,cc,tmp,Full.Fwd(i,tmp,ct),p))
  | Full.Close (i,c) -> Core.Close (loc2ast i,c)
  | Full.Exit i -> Core.Exit (loc2ast i)
  | Full.Wait (i,c,p) -> Core.Wait (loc2ast i,c,desugarProc this (CS.remove scope c) p)
  | Full.Fwd (i,c1,c2) -> Core.Fwd (loc2ast i,c1,c2)
  | Full.External (i,c,br) -> Core.External (loc2ast i,c,LM.map br (desugarProc this scope))
  | Full.Internal (i,c,l,p) -> Core.Internal (loc2ast i,c,l,desugarProc this scope p)
  | Full.Abort i -> (* We abort by having an empty external choice. To make the 
                       typing work out we also need an unproductive process. *)
    desugarProc this scope 
    (let tmpc = (i,Lin ("abort_"^priv_name ()))
    in Full.Bind(i,tmpc,Full.Let(i,`M (Full.MonT (i,Some (Full.Intern (i,Linear,LM.empty)),[]))
                                ,(i,"_abort_"),[]
                                ,Full.Monad(i,Some tmpc,Full.TailBind(i,tmpc,Full.Var(i,(i,"_abort_")),[]),[])
                                ,Full.Var (i,(i,"_abort_"))),[]
                ,Full.External(i,tmpc,LM.empty)))
  | Full.TailBind (i,c,e,cs) -> Core.TailBind (loc2ast i,c,desugarExp e,cs)
  | Full.IfP (i,e,pt,pf) -> 
    desugarProc this scope (Full.CaseP (i,e,SM.of_alist_exn [("True",([],pt));("False",([],pf))]))
  | Full.Seq (i,e,p) ->
    desugarProc this scope (Full.LetP (i,`M (Full.Comp (i,"()",[])),(i,"Seq_"^priv_name ()),[],e,p))
  | Full.LetP (i,t,x,xs,e,p) ->
    desugarProc this scope (Full.TailBind (i,this,Full.Let(i,t,x,xs,e,Full.Monad(i,Some this,p,CS.to_list scope))
                                          ,CS.to_list scope))
  | Full.CaseP (i,e,br) -> 
    desugarProc this scope (Full.TailBind (i,this,Full.Case(i,e,SM.map br (fun (pat,p) ->
                                            (pat,Full.Monad(i,Some this,p,CS.to_list scope)))),CS.to_list scope))
  | Full.InTy (l,x,c,p) -> Core.InputTy (loc2ast l,x,c,desugarProc this scope p)
  | Full.OutTy (l,c,s,p) -> Core.OutputTy (loc2ast l,c,s,desugarProc this scope p)
  | Full.ShftUpL (l,c1,c2,p) -> Core.ShftUpL (loc2ast l,c1,c2
                                             ,desugarProc this (CS.add (CS.remove scope c2) c1) p)
  | Full.ShftDwR (l,c1,c2,p) -> Core.ShftDwR (loc2ast l,c1,c2
                                             ,desugarProc c2 scope p)
  | Full.SendSync (l,c,p) when cvar_eq c this -> Core.ShftDwR (loc2ast l,c,c,desugarProc this scope p)
  | Full.SendSync (l,c,p) -> Core.ShftUpL (loc2ast l,c,c, desugarProc this scope p)
  | Full.RecvSync (l,c,p) -> Core.InputC (loc2ast l,(if cvar_eq c this 
                                                     then ref `UpCastR else ref `DwCastL)
                                         ,c,c,desugarProc this scope p)

(* Since we know there can be no type variables in scope, generalizing top level bindings
   is much easier than normal *)
let rec desugartoplet (tin:Full.toplet) : (fvar * Pure.ptype * fvar list * Full.exp) =
  match tin with
  | Full.TopExp (x,`P p,None,pats,e)  -> desugartoplet (Full.TopExp (x, `P p,Some [],pats,e))
  | Full.TopExp (x,`P (Pure.Poly(mvs,svs,p)),Some qs',pats,e)  -> 
    (* TODO is this really the best place to check this? *)
    (* TODO add a test case to typeerrors *)
    if not (qs' = svs) then errr (Full.locE e) "Mismatched session type quantifiers";
    (* TODO Is it really safe to generalize the mtype vars here? *)
    (x,(Pure.Poly((SS.to_list (Full.freeMVarsMPure p)),svs,p)),pats,e)
  | Full.TopExp (f1,`M m,qs,pats,e) -> desugartoplet (
    Full.TopExp (f1,`P (Pure.Poly((SS.to_list (Full.freeMVarsMPure m)),[],m)),qs,pats,e))
  | Full.TopMon (name,tysig,qs,pats,c,proc,cs) ->
    desugartoplet (Full.TopExp (name,tysig,qs,pats,(Full.Monad ((fst c),Some c,proc,cs))))
  | Full.TopDet (name,tysig,qs,pats,loc,proc,cs) ->
    desugartoplet (Full.TopExp (name,tysig,qs,pats,(Full.Monad (loc,None,proc,cs))))

let rec desugarTop (tin:Full.toplvl) : Core.toplvl list =
  match tin with (* TODO do we need to return lists here? *)
  | Full.ServDecl (f,s) -> [Core.ServDecl (f,s)]
  | Full.TopLets_ def -> desugarTop (Full.TopLets (desugartoplet def))
  | Full.TopLets (f,t,[],e) -> [Core.TopLet (f,`P t,desugarExp e)]
  | Full.TopLets (f,t,x::xs,e) -> [Core.TopLet (f,`P t,desugarExp (Full.Fun (fst f,x,xs,e)))]
  | Full.TopProc procs -> (* See tests/sugar for what this is doing *)
    let go (acc: Full.proc -> Full.proc) ((c,p) : cvar*Full.proc) : (Full.proc -> Full.proc) =
        (fun (cont : Full.proc) ->
         let tmpe = (fst c,"_mix_desugar_"^priv_name ())
         and tmpc = (fst c,Lin ("_mix_desugar_"^priv_name ()))
         in Full.LetP(fst c
                     ,`M (Pure.MonT(fst c,Some (Pure.Stop (fst c,Linear)),[]))
                     ,tmpe
                     ,[]
                     ,Full.Monad(fst c,Some c,p,[])
                     ,Full.Bind(fst c,tmpc,(Full.Var(fst c, tmpe)),[]
                               ,acc (Full.Wait(fst c,tmpc,cont)))))
    in (match procs with
       | [] -> failwith "BUG desugaring found empty TopProc"
       | [(c,p)] -> [Core.TopProc (c,desugarProc c CS.empty p)]
       | (c,_)::_ ->  
           let context = (List.fold_left procs ~init:(fun x -> x) ~f:go)
           and tmp = (fst c,Lin(priv_name ()))
           in desugarTop (Full.TopProc [(tmp,context (Full.Close(fst tmp,tmp)))]))
  | Full.MTypeDecl (t,fs,cm) -> [Core.MTypeDecl (t,fs,cm)]
  | Full.STypeDecl (modedecl,t,fs,s) -> 
    (* Check that the type is contractive (i.e., doesn't immediately recurse) *)
    (match s with
    | Pure.SComp (_,n,_) when n = snd t -> errr (fst t) "Non-contractive type"
    | _ -> ());

    (* Record the mode of the type. This might be able to be merged with some other step. *) 
    Pure.declModes := SM.add !Pure.declModes (snd t) modedecl;
   
    (* Record the polarity of the type *)
    Pure.declPoles := SM.add !Pure.declPoles (snd t) (Pure.polarity s);
    sessionQs := SM.add !sessionQs (snd t) fs;

    (* Check that the mode of the type matches its declaration. A Linear mode is ok
       here because it will be fixed by later propagation of modedecl *)
    if not (modedecl = Pure.getmode s || Pure.getmode s = Linear)
    then errr (fst t) ("Expected an "^string_of_mode modedecl^" type but found a "
                      ^string_of_mode (Pure.getmode s)^" type.");

    (* If t is mentioned recursively we need to add mu's to it.
       To ensure regularity we enforce that recursive calls cannot have arguments.
       Like with pretty printing we use a reference to denote we actually did something. *)
    let this : (string*(srcloc * [`A of fvar | `M of Pure.mtype | `S of Pure.stype] list) list) option ref = ref None in
    let getThis (l:srcloc) (params : [`A of fvar | `M of Pure.mtype | `S of Pure.stype] list) : string = 
        (match !this with 
        | Some (s,argss) -> this := Some (s,((l,params) :: argss)); s 
        | None -> 
          let tmp = snd t^"_"^priv_name() in this := Some (tmp,[(l,params)]); tmp)
    in let rec goS min sin = (* min refers to the desired mode. This is to allow atype and
                                utype to mangle their declared modes a bit. TODO this
                                should be reworked to split the mode mangling out more
                                cleanly. *)
           match sin with
           | Pure.SComp (l,n,args) when n = snd t -> 
               let x = getThis l args
               in Pure.SVar (l,(Linear,x)) (* TODO hardcoded mode *)
           | Pure.SComp (l,n,args) ->
             let args' = List.map args (fun arg -> match arg with
                                                   | `A x -> `A x
                                                   | `M x -> `M (goM x)
                                                   | `S x -> `S (goS min x))
             in Pure.SComp (l,n,args')
           | Pure.SVar (x,y) -> Pure.SVar (x,y)
           | Pure.Stop (l,_) -> Pure.Stop (l,min)
           | Pure.Mu (l,x,s,name,args) ->
             let args' = List.map args (fun arg -> match arg with
                                                   | `A x -> `A x
                                                   | `M x -> `M (goM x)
                                                   | `S x -> `S (goS min x))
             in Pure.Mu (l,x,goS min s,name,args')
           | Pure.TyInD (l,_,m,s) -> Pure.TyInD(l,min,goM m,goS min s)
           | Pure.TyOutD (l,_,m,s) -> Pure.TyOutD(l,min,goM m,goS min s)
           | Pure.TyInC (l,_,s1,s2) -> Pure.TyInC(l,min,goS min s1,goS min s2)
           | Pure.TyOutC (l,_,s1,s2) -> Pure.TyOutC(l,min,goS min s1,goS min s2)
           | Pure.Intern (l,_,lm) -> Pure.Intern (l,min,LM.map lm (goS min))
           | Pure.Extern (l,_,lm) -> Pure.Extern (l,min,LM.map lm (goS min))
           | Pure.Forall (l,_,x,s) -> Pure.Forall (l,min,x,goS min s)
           | Pure.Exists (l,_,x,s) -> Pure.Exists (l,min,x,goS min s)
           | Pure.ShftUp (l,m,s) -> 
             if m = min
             then Pure.ShftUp(l,m,goS Linear s)
             else failwith ("desugarer expected "^string_of_mode min^" but found "^Pure.string_of_stype s)
           | Pure.ShftDw (l,m,s) -> 
             if m = min
             then Pure.ShftDw(l,m,goS Linear s)
             else failwith ("desugarer expected "^string_of_mode min^" but found "^Pure.string_of_stype s)
           | Pure.Bang (l,s) -> (* TODO examples using this *)
             (match Pure.getmode s with
             | Linear -> Pure.ShftUp(l,Intuist, goS Linear s)
             | Affine -> Pure.ShftUp(l,Intuist, goS Affine s)
             | Intuist -> goS min (Pure.Sync (l,s)))
           | Pure.TyAt (l,s) -> (* TODO examples using this *)
             (match Pure.getmode s with
             | Linear -> Pure.ShftUp(l,Affine, goS Affine s)
             | Affine -> goS min (Pure.Sync (l,s))
             | Intuist -> Pure.ShftDw(l,Affine, goS Intuist s))
           | Pure.Prime (l,s) -> (* TODO examples using this *)
             (match Pure.getmode s with
             | Linear -> goS min (Pure.Sync (l,s))
             | Affine -> Pure.ShftDw(l,Linear, goS Affine s)
             | Intuist -> Pure.ShftDw(l,Linear, goS Intuist s))
           | Pure.Sync (l,s) ->
             (match Pure.polarity s with
             | `Neg -> goS min (Pure.ShftDw(l,Linear, s))
             | `Pos -> goS min (Pure.ShftUp(l,Linear, s)))
       and goM (tin:Pure.mtype) : Pure.mtype =
           match tin with
           | Pure.MVar (l,x) -> Pure.MVar (l,x)
           | Pure.Comp (l,n,args) -> Pure.Comp(l,n,List.map args (function
                                                              | `A a -> `A a
                                                              | `M m -> `M (goM m)
                                                              | `S s -> `S (goS Linear s)))
           | Pure.MonT (l,Some s,ss) -> Pure.MonT(l,Some (goS Linear s),List.map ss (goS Linear))
           | Pure.MonT (l,None,ss) -> Pure.MonT (l,None,List.map ss (goS Linear))
       in let s' = goS modedecl s
          in match !this with
             | Some (x,argss) -> 
               (* Search for mismatched paramters *)
               List.iter argss ~f:(fun (l,args) ->
                 if not (List.length fs = List.length args)
                 then errr l "Recursive calls must have identical parameters";
                 List.iter2_exn fs args ~f:(fun q mt -> 
                   match q,mt with
                   | `M x,`M (Pure.MVar (_,y)) when x = y -> ()
                   | `S x,`S (Pure.SVar (_,y)) when x = y -> ()
                   | _ -> errr l "Recursive calls must have identical paramters"));
              let qs' = List.map fs (fun q -> match q with 
                                              | `M x -> `M (Pure.MVar (fst t,x))
                                              | `S x -> `S (Pure.SVar (fst t,x)))
              in [Core.STypeDecl (t,fs,Pure.Mu(Pure.locS s',(Linear,x),s',snd t,qs'))] (* TODO hardcoded mode *)
             | None -> [Core.STypeDecl (t,fs,s')]
