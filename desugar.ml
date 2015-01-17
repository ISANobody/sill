open Base
open Core.Std
open Vars
open Syntax
open Types

let loc2ast l = { Syntax.Core.linenum = l.lnum; Syntax.Core.charnum = l.cnum; 
                  Syntax.Core.affineFrees = ref CS.empty }

let freshMode v = let name = (priv_name ())
                  in match v with
                     | (l,Lin _) -> (l,Lin name)
                     | (l,Aff _) -> (l,Aff name)
                     | (l,Shr _) -> (l,Shr name)

let rec desugarExp (ein:Full.exp) : Core.exp =
  match ein with
  | Full.Var (i,(_,"not")) -> 
    desugarExp (Full.Let (i,`M (Full.Comp("->",[`M (Full.Comp("Bool",[]))
                                               ;`M (Full.Comp("Bool",[]))]))
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
  | Full.PolyApp (i,x,args) -> (* TODO better disambiguation/error reporting here *)
    let args' = List.map args (function
                              | `A (Pure.TyApp (name,a)) when SM.mem !sessionQs (snd name) -> 
                                    `S (Pure.tyapp2stype (Pure.TyApp (name,a)))
                              | `A a -> `M (Pure.tyapp2mtype a)
                              | `M m -> `M m
                              | `S s -> `S s)
    in Core.PolyApp(loc2ast i,x,args')

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
    let tmp = (fst ct,Lin (priv_name ()))
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
    (let tmpc = (i,Lin (priv_name ()))
    in Full.Bind(i,tmpc,Full.Let(i,`M (Full.MonT (Some (Full.Intern (Linear,LM.empty)),[]))
                                ,(i,"_abort_"),[]
                                ,Full.Monad(i,Some tmpc,Full.TailBind(i,tmpc,Full.Var(i,(i,"_abort_")),[]),[])
                                ,Full.Var (i,(i,"_abort_"))),[]
                ,Full.External(i,tmpc,LM.empty)))
  | Full.TailBind (i,c,e,cs) -> Core.TailBind (loc2ast i,c,desugarExp e,cs)
  | Full.IfP (i,e,pt,pf) -> 
    desugarProc this scope (Full.CaseP (i,e,SM.of_alist_exn [("True",([],pt));("False",([],pf))]))
  | Full.Seq (i,e,p) ->
    desugarProc this scope (Full.LetP (i,`M (Full.Comp ("()",[])),(i,priv_name ()),[],e,p))
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

let rec desugartoplet (tin:Full.toplet) : Full.toplet =
  match tin with
  | Full.TopExp _  -> tin
  | Full.TopMon (name,tysig,pats,c,proc,cs) ->
    desugartoplet (Full.TopExp (name,tysig,pats,(Full.Monad ((fst c),Some c,proc,cs))))
  | Full.TopDet (name,tysig,pats,loc,proc,cs) ->
    desugartoplet (Full.TopExp (name,tysig,pats,(Full.Monad (loc,None,proc,cs))))

(* This probably is a reflection of poor design somewhere else *)
let getLetType (e:Full.toplet) : Full.mtype =
  match desugartoplet e with
  | Full.TopExp (_,(_,`M t),_,_) -> t
  | _ -> failwith "BUG getLetType of non-TopExp `M"
let getLetArgs (e:Full.toplet) : fvar * fvar list =
  match desugartoplet e with
  | Full.TopExp (_,_,x::xs,_) -> (x,xs)
  | Full.TopExp (name,_,_,_) -> errr (fst name) "mutual recursion of non-functions"
  | _ -> failwith "BUG getLetArgs of non-TopExp"
let getLetBinding (e:Full.toplet) : Full.exp =
  match desugartoplet e with
  | Full.TopExp (_,_,_,b) -> b
  | _ -> failwith "BUG getLetBinding of non-TopExp"


(* We special case the time when we don't need to handle mutual recursion. If we had a
   general purpose optimization phase, perhaps "remove single constructor enums" would
   allow us to collapse these cases without an evaluation performance hit. *)
let rec desugarTop (tin:Full.toplvl) : Core.toplvl list =
  match tin with
  | Full.ServDecl (f,s) -> [Core.ServDecl (f,s)]
  | Full.TopLets m -> 
    if FM.length m = 1
    then [Core.TopLet (List.nth_exn (FM.keys m) 0
         ,(let Full.TopExp (_,(_,t),_,_) = desugartoplet (List.nth_exn (FM.data m) 0) in t)
         ,desugarExp (match desugartoplet (List.nth_exn (FM.data m) 0) with
                     | Full.TopExp (name,(signame,tysig),pats,e) -> 
                       (match pats with
                       | [] -> e
                       | x::xs -> Full.Fun ((fst name),x,xs,e))
                     | _ -> failwith "BUG desugarTop Binding in non-cannonical form")
         )]
    else (* To desugar a mutually recursive function we do the following:
            1) Create an enumeration to select between which of the functions our combined
               function should behave as
            2) Create a type to package up the (possibly) distinct types of each function.
            3) Create the combined function. To avoid name mangling in the body, we first
               create local copies of the wrappers that present a mutually recursive view
               to the outside world.
            4) Reproduce the wrappers as top level bindings *)
      let prefix = "_mutual-recursion-desugar_" ^intercal string_of_fvar "_" (FM.keys m)
      and brvar = ({lnum=0;cnum=0},priv_name ()) in
      let wrapperBody (f:fvar) (v:fvar) : Full.exp = (* TODO is v needed? *)
        Full.App(fst f
                ,Full.Case(fst f
                          ,Full.App(fst f
                                   ,Full.Var(fst f,(fst f,prefix^"_recursor_"))
                                   ,Full.Sat(fst f,prefix^"_selector_"^string_of_fvar f,[]))
                          ,SM.singleton (prefix^"_result_"^string_of_fvar f)
                                        ([(fst f,"_")],Full.Var(fst f,(fst f,"_"))))
                ,Full.Var(fst f,v))
      in let wrapper (f:fvar) (e:Full.toplet) (body:Full.exp) : Full.exp = 
        Full.Let(fst f,`M (getLetType e),f,[fst (getLetArgs e)]
                ,wrapperBody f (fst (getLetArgs e))
                ,body)
      and (* We want a consistent list of the polymorphic variables in our combined type *)
          polymangle = List.map (List.dedup
                                (List.concat_map (FM.data m) (fun e -> SS.to_list 
                                          (Full.freeMVarsMPure (getLetType e)))))
                                (fun x -> `M x)
      and selector : Full.exp = (* The big case statement selecting behavior *)
         (Full.Case({cnum=0;lnum=0}
                   ,Full.Var({lnum=0;cnum=0},brvar)
                   ,SM.of_alist_exn (List.map (FM.to_alist m)
                       (fun (f,e) -> (prefix^"_selector_"^string_of_fvar f,([],
                        Full.Sat({lnum=0;cnum=0},prefix^"_result_"^string_of_fvar f,[
                        Full.Fun(Full.locToplet e
                                ,fst (getLetArgs e)
                                ,snd (getLetArgs e)
                                ,getLetBinding e)])))))))
      in
      List.concat_map (
      (* Create the input combining type *)
      [ Full.MTypeDecl (({lnum=0;cnum=0},prefix^"_selector_"),[],SM.of_alist_exn (List.map (FM.keys m)
                     (fun f -> (prefix^"_selector_"^string_of_fvar f,[]))))
      ]@

      (* Create the bundled type. For later substitution purposes,
         we should be doing some name mangling of type variables.
         Instead we'll require users to protect themselves. This is horrible. *)
      [ Full.MTypeDecl (({lnum=0;cnum=0},prefix^"_result_"),
                     polymangle
                     ,SM.of_alist_exn (List.map (FM.to_alist m)
                     (fun (f,e) -> (prefix^"_result_"^string_of_fvar f,
                                    [getLetType e]))))
      ]@
        
      (* Create the combined function *)
      [ Full.TopLets(FM.singleton ({lnum=0;cnum=0},prefix^"_recursor_")
        (Full.TopExp (({lnum=0;cnum=0},prefix^"_recursor_")
           ,(({lnum=0;cnum=0},prefix^"_recursor_")
           ,`M (Pure.Comp("->"
                           ,[`M (Pure.Comp(prefix^"_selector_",[]))
                            ;`M (Pure.Comp(prefix^"_result_"
                                      ,List.map polymangle 
                                                (fun _ -> `M (Pure.MVar (priv_name ())))))])))
           ,[brvar]
           ,FM.fold m ~f:(fun ~key:f ~data:e acc -> wrapper f e acc) ~init:selector
      )))]@

      (* Create the wrappers for external use *)
      List.map (FM.to_alist m)
        (fun (f,e) -> Full.TopLets 
           (FM.singleton f 
              (Full.TopExp (f,(f,`M (getLetType e)),[brvar],wrapperBody f brvar))))
      ) desugarTop
  | Full.TopProc procs -> (* See tests/sugar for what this is doing *)
    let go (acc: Full.proc -> Full.proc) ((c,p) : cvar*Full.proc) : (Full.proc -> Full.proc) =
        (fun (cont : Full.proc) ->
         let tmpe = (fst c,"_mix_desugar_"^priv_name ())
         and tmpc = (fst c,Lin ("_mix_desugar_"^priv_name ()))
         in Full.LetP(fst c
                     ,`M (Pure.MonT(Some (Pure.Stop Linear),[]))
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
    (* First record the mode of the type. This might be able to be merged with some other step. *) 
    Pure.declModes := SM.add !Pure.declModes (snd t) modedecl;
    sessionQs := SM.add !sessionQs (snd t) fs;

    (* If t is mentioned recursively we need to add mu's to it.
       To ensure regularity we enforce that recursive calls cannot have arguments.
       Like with pretty printing we use a reference to denote we actually did something. *)
    let this : (string*(srcloc * [`A of fvar | `M of Pure.mtype | `S of Pure.stype] list) list) option ref = ref None in
    let getThis (l:srcloc) (params : [`A of fvar | `M of Pure.mtype | `S of Pure.stype] list) : string = 
        (match !this with 
        | Some (s,argss) -> this := Some (s,((l,params) :: argss)); s 
        | None -> let tmp = priv_name() in this := Some (tmp,[(l,params)]); tmp)
    in let rec goS min sin =
           match sin with
           | Pure.SComp (l,n,args) when n = snd t -> Pure.SVar (l,(Linear,getThis l args)) (* TODO hardcoded mode *)
           | Pure.SComp (l,n,args) ->
             let args' = List.map args (fun arg -> match arg with
                                                   | `A x -> `A x
                                                   | `M x -> `M (goM x)
                                                   | `S x -> `S (goS min x))
             in Pure.SComp (l,n,args')
           | Pure.SVar (x,y) -> Pure.SVar (x,y)
           | Pure.Stop _ -> Pure.Stop min
           | Pure.Mu (x,s,name,args) ->
             let args' = List.map args (fun arg -> match arg with
                                                   | `A x -> `A x
                                                   | `M x -> `M (goM x)
                                                   | `S x -> `S (goS min x))
             in Pure.Mu (x,goS min s,name,args')
           | Pure.TyInD (_,m,s) -> Pure.TyInD(min,goM m,goS min s)
           | Pure.TyOutD (_,m,s) -> Pure.TyOutD(min,goM m,goS min s)
           | Pure.TyInC (_,s1,s2) -> Pure.TyInC(min,goS min s1,goS min s2)
           | Pure.TyOutC (_,s1,s2) -> Pure.TyOutC(min,goS min s1,goS min s2)
           | Pure.Intern (_,lm) -> Pure.Intern (min,LM.map lm (goS min))
           | Pure.Extern (_,lm) -> Pure.Extern (min,LM.map lm (goS min))
           | Pure.Forall (_,x,s) -> Pure.Forall (min,x,goS min s)
           | Pure.Exists (_,x,s) -> Pure.Exists (min,x,goS min s)
           | Pure.ShftUp (m,s) -> 
             if m = min
             then Pure.ShftUp(m,goS Linear s)
             else failwith ("desugarer expected "^string_of_mode min^" but found "^Pure.string_of_stype s)
           | Pure.ShftDw (m,s) -> 
             if m = min
             then Pure.ShftDw(m,goS Linear s)
             else failwith ("desugarer expected "^string_of_mode min^" but found "^Pure.string_of_stype s)
           | Pure.Bang s -> failwith "desugar Bang"
           | Pure.TyAt s -> failwith "desugar At"
           | Pure.Prime s -> failwith "desugar Prime"
       and goM (tin:Pure.mtype) : Pure.mtype =
           match tin with
           | Pure.MVar x -> Pure.MVar x
           | Pure.Comp (n,args) -> Pure.Comp(n,List.map args (function
                                                              | `A a -> `A a
                                                              | `M m -> `M (goM m)
                                                              | `S s -> `S (goS Linear s)))
           | Pure.MonT (Some s,ss) -> Pure.MonT(Some (goS Linear s),List.map ss (goS Linear))
           | Pure.MonT (None,ss) -> Pure.MonT (None,List.map ss (goS Linear))
       in let s' = goS modedecl s
          in match !this with
             | Some (x,argss) -> 
               (* Search for mismatched paramters *)
               List.iter argss ~f:(fun (l,args) ->
                 if not (List.length fs = List.length args)
                 then errr l "Recursive calls must have identical parameters";
                 List.iter2_exn fs args ~f:(fun q mt -> 
                   match q,mt with
                   | `M x,`M (Pure.MVar y) when x = y -> ()
                   | `S x,`S (Pure.SVar (_,y)) when x = y -> ()
                   | _ -> errr l "Recursive calls must have identical paramters"));
              let qs' = List.map fs (fun q -> match q with 
                                              | `M x -> `M (Pure.MVar x)
                                              | `S x -> `S (Pure.SVar (fst t,x)))
              in [Core.STypeDecl (t,fs,Pure.Mu((Linear,x),s',snd t,qs'))] (* TODO hardcoded mode *)
             | None -> [Core.STypeDecl (t,fs,s')]
