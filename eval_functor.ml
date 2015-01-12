open Base
open Core.Std
open Value
open Syntax.Core
open Vars
open Eval_exp
open Connection
open Eval_abstract

module type Evaluator =
sig
  type channel
  val eval_proc : (value SM.t) -> (shrsrc CM.t) -> (channel CM.t) -> proc -> unit
  val eval_top : (value SM.t) -> toplvl list -> unit
  val tail_bind_hook : (unit -> unit) ref
end

module MkEvaluator = functor (I:Impl) ->
struct
  type channel = I.channel
  
  module Exp = MkExpEvaluator(I)

  let tail_bind_hook : (unit -> unit) ref = ref (fun () -> ())

  (* env  -- The functional environment
     senv -- The shared/replicable environment
     cenv -- The linear environment
     pin  -- The actual process to evaluate *)
  let rec eval_proc (env:value SM.t) (senv: shrsrc CM.t) (cenv:channel CM.t) (pin:proc) =
    let chanfind rule (c:cvar) : I.channel =
      if CM.mem cenv c
       then CM.find_exn cenv c
       else errr (fst c) (rule^": channel "^string_of_cvar c^" not found. BUG.")
    and shrfind (c:cvar) : shrsrc =
        if not (is_shr c) then errr (fst c) "tried to look up non-persistent variable as shared. BUG.";
        match CM.find senv c with
        | Some s -> s
        | None -> errr (fst c) ("channel "^string_of_cvar c^" not found. BUG.")
    and eval_trace (s:string) : unit =
        if !live_trace_flag then print_endline (loc2str (locP pin)^" "^s);
        if !eval_trace_flag then I.log (loc2str (locP pin)^" "^s) else ()
    in let waitone c = 
             if I.is_Term (I.read_comm c)
             then ()
             else failwith "received non-Term. BUG."
       in
  (* First free any affine channels that need it *)
  CS.iter !((getinfoP pin).affineFrees) (fun c -> eval_trace ("free "^string_of_cvar c);
                                                  I.free (chanfind "free" c));

  (* Proceed with evaluation *)
  match pin with
  | Close (_,c) ->
    eval_trace "close";
    I.write_comm (chanfind "close" c) (I.mkTerm ());
    I.procExit ()
  | Exit _ -> eval_trace "detached exit";  I.procExit ()
  | Register (_,n,c,p) -> I.register (snd n) (chanfind "register" c);
                          eval_proc env senv cenv p
  | Service (_,c,n,p) -> eval_proc env senv (CM.add cenv c (I.request (snd n))) p
  | Wait (_,c,p) ->
    eval_trace "wait";
    waitone (chanfind "wait" c);
    eval_proc env senv cenv p
  | OutputD (i,c,e,p) -> 
    let v = Exp.eval_exp e env
    in eval_trace ("output "^string_of_value v);
       I.write_comm (chanfind "OutputD" c) (I.valComm v);
       eval_proc env senv cenv p
  | InputD (i,x,c,p) ->
    (match I.getVal (I.read_comm (chanfind "InputD" c)) with
    | Some (Boxed (t,v)) -> 
      eval_trace ("input "^string_of_value v);
      eval_proc (SM.add env (snd x) v) senv cenv p
    | Some v -> 
      if !dynchecks_flag
      then errr (fst x) " received unboxed data. BUG."
      else eval_trace ("input "^string_of_value v);
           eval_proc (SM.add env (snd x) v) senv cenv p
    | None -> errr (fst x) " found non-value. BUG.")
  | TailBind (_,c,e,cs) ->
    Thread.yield ();
    !tail_bind_hook ();
    eval_trace "tail-bind";
    (match Exp.eval_exp e env with
    | MonV (Some c',cs',p,env') ->
      let cenv' = CM.of_alist_exn (filter_map2_exn (c::cs) (c'::cs') 
                                                    (fun x x' -> if not (is_shr x)
                                                                 then Some (x',chanfind "tail-bind" x)
                                                                 else None))
      and senv' = CM.of_alist_exn (filter_map2_exn cs cs' 
                                                   (fun x x' -> if is_shr x 
                                                                then Some (x',shrfind x)
                                                                else None))
      in eval_proc env' senv' cenv' p
    | MonV (None,cs',p,env') -> errr (locE e) "BUG. Tried to tail-foward from detached type."
    | _ -> errr (locE e) "bind of non-monad. BUG.")
  | Bind (i,c,e,cs,p) when not (is_shr c) ->
    Thread.yield ();
    eval_trace "bind";
    (match Exp.eval_exp e env with
    | MonV (Some c',cs',p',env') ->
      let cenv' = CM.of_alist_exn (filter_map2_exn cs cs' 
                                                    (fun x x' -> if not (is_shr x)
                                                                 then Some (x',chanfind "{ }E" x)
                                                                 else None))
      and senv' = CM.of_alist_exn (filter_map2_exn cs cs' 
                                                   (fun x x' -> if is_shr x 
                                                                then Some (x',shrfind x)
                                                                else None)) in
      let ch = I.spawnRemote env' senv' cenv' p' c'
      in eval_proc env senv (CM.add cenv c ch) p
    | MonV (None,cs',p',env') ->
      let cenv' = CM.of_alist_exn (filter_map2_exn cs cs' 
                                                    (fun x x' -> if not (is_shr x)
                                                                 then Some (x',chanfind "{ }E" x)
                                                                 else None))
      and senv' = CM.of_alist_exn (filter_map2_exn cs cs' 
                                                   (fun x x' -> if is_shr x 
                                                                then Some (x',shrfind x)
                                                                else None)) in
      let ch = I.spawnRemote env' senv' cenv' p' ((locP pin),Lin (priv_name ()))
      in eval_proc env senv (CM.add cenv c ch) p
    | _ -> errr (locE e) " bind of non-monad. BUG.")
  | Bind (_,u,e,us,p) when is_shr u ->
    Thread.yield ();
    eval_trace "sbind";
    (match Exp.eval_exp e env with
    | MonV (Some c',cs',p',env') ->
      let senv' = CM.of_alist_exn (filter_map2_exn us cs' 
                                                   (fun x x' -> if is_shr x 
                                                                then Some (x',shrfind x)
                                                                else errr (fst x') "Lin in sbind. BUG."))
      in eval_proc env (CM.add senv u (ShrSrc (c',p',env,senv'))) cenv p
    | MonV (None,_,_,_) -> errr (locE e) " BUG. Shared bind of detatched monad"
    | _ -> errr (locE e) " bind of non-monad. BUG.")
  | Bind _ -> failwith "eval_proc -Wall fix, prior patterns have guards"
  | OutputC (i,c,d,pd,p) ->
    eval_trace "outputC";
    let ch = I.spawn env senv cenv pd d
    in I.write_comm (chanfind "OutputC" c) (I.chanComm ch);
       eval_proc env senv cenv p
  | InputC (i,disambig,cx,cc,p) ->
    (match !disambig with
    | `Tensor -> 
      eval_trace "inputC";
      (match I.getChan (I.read_comm (chanfind "InputC" cc)) with
      | Some ch -> eval_proc env senv (CM.add cenv cx ch) p
      | None -> errr (fst cc) " found non-Chan. BUG.")
    | `DwCastL -> 
      eval_trace "ShftDwL";
      if var2mode cx = Intuist
      then (match I.getVal (I.read_comm (chanfind "DwCastL" cc)) with
           | Some (Shared s) -> eval_proc env (CM.add senv cx s) cenv p
           | Some _ | None -> errr (fst cc) "non-Shr in ShftDwL. BUG.")
      else (match I.getChan (I.read_comm (chanfind "ShftDwnL" cc)) with
           | Some ch -> eval_proc env senv (CM.add cenv cx ch) p
           | None -> errr (fst cc) " found non-Chan. BUG.")
    | `UpCastR -> 
      eval_trace "UpCastR";
      if var2mode cc = Intuist
      then (* Warning this assumes that the provider channel was set correctly *)
           eval_proc env senv cenv p
      else (match I.getChan (I.read_comm (chanfind "UpcastR" cc)) with
           | Some ch -> eval_proc env senv (CM.add cenv cx ch) p
           | None -> errr (fst cc) " found non-Chan. BUG."))
  | External (i,c,ps) ->
    if LM.is_empty ps
    then errr (ast2loc i) "Empty Case Abort"
    else (match I.getLab (I.read_comm (chanfind "External" c)) with
         | Some l -> if not (LM.mem ps l)
                    then errr (ast2loc i) ("External choice, no branch for "
                                          ^string_of_label l^" BUG.")
                    else eval_trace ("external "^string_of_label l);
                         eval_proc env senv cenv (LM.find_exn ps l)
         | None -> errr (fst c) "non-label in External. BUG.")
  | Internal (_,c,l,p) ->
    eval_trace ("internal "^string_of_label l);
    I.write_comm (chanfind "Internal" c) (I.labComm l);
    eval_proc env senv cenv p
  | Fwd (_,c,d) ->
    eval_trace "forward";
    I.forward (chanfind "Forward" c) (chanfind "Forward" d)
  | InputTy (_,_,c,p) ->
    eval_trace "inputTy";
    (match I.getLab (I.read_comm (chanfind "InputTy" c)) with
    | Some (_,"_FakeTy_") -> eval_proc env senv cenv p
    | _ -> errr (fst c) "BUG. Found wrong message for inputTy")
  | OutputTy (_,c,_,p) ->
    eval_trace "outputTy";
    I.write_comm (chanfind "OutputTy" c) (I.labComm (nullloc,"_FakeTy_"));
    eval_proc env senv cenv p
  | ShftUpL (_,c1,c2,p) -> (* n.b., c2 records modality already *)
    eval_trace "ShftUpL";
    if var2mode c2 = Intuist
    then let ShrSrc (d,dp,env',senv') = shrfind c2
         in let ch = I.spawn env' senv' CM.empty dp d;
            in eval_proc env senv (CM.add cenv c1 ch) p
    else let (ch,ch') = I.newChan ()
         in I.write_comm (chanfind "UpcastL" c2) (I.chanComm ch);
            eval_proc env senv (CM.add cenv c1 ch') p
  | ShftDwR (_,c1,c2,p) ->
    eval_trace "ShftDwR";
    if var2mode c2 = Intuist
    then (match p with
         | InputC (_,ambig,c3,c4,p') when !ambig = `UpCastR ->
           I.write_comm (chanfind "ShftDwR" c1) (I.valComm (Shared (ShrSrc (c3,p',env,senv))))
         | _ -> errr (locP pin) "BUG ShftDwR unrestricted p' problems")
    else let ch = I.spawn env senv cenv p c2
         in I.write_comm (chanfind "ShftDwR" c1) (I.chanComm ch)

  let rec eval_top (env:value SM.t) (esin:toplvl list) : unit =
    match esin with
    | [] -> Pervasives.exit 0
    | TopLet (f,_,e)::es -> clearmaps ();
                            let v = Exp.eval_exp e (SM.add env (snd f) (Recvar(snd f,e,env)))
                            in eval_top (SM.add env (snd f) v) es 
    | TopProc (ch,p)::es -> clearmaps ();
                            let chan = I.spawn env CM.empty CM.empty p ch
                            in if I.is_Term (I.read_comm chan)
                               then eval_top env es
                               else I.abort "Got non-Term at top-proc. BUG."
    | Pass::es -> eval_top env es
    | ServDecl _::es -> eval_top env es
    | MTypeDecl _::es -> eval_top env es
    | STypeDecl _::es -> eval_top env es
end
