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
  type proc_local
  val eval_proc : (value SM.t) -> (shrsrc CM.t) -> (channel CM.t) -> proc -> proc_local -> unit
  val eval_top : toplvl list -> unit
  val tail_bind_hook : (proc_local -> unit) ref
end

module MkEvaluator = functor (I:Impl) ->
struct
  type channel = I.channel
  type proc_local = I.proc_local

  (* We need a state to start with *)
  let newstateCounter = ref 0
  let newstate () = incr newstateCounter; 
      { I.id               = [!newstateCounter] 
      ; I.childCounter     = ref 0
      ; I.focusCache       = ref None
      ; I.focusCounter     = ref 0
      ; I.unfocusCounter   = ref 0
      ; I.numTailbinds = ref 0 }

(* Given a local state compute the state its child should start with.
   Maybe this should return a mutated parent state instead of assuming references *)
  let childState (s:proc_local) : proc_local =
    incr s.I.childCounter;
    { I.id = s.I.id@[!(s.I.childCounter)]
    ; I.childCounter = ref 0
    ; I.focusCache = ref None
    ; I.focusCounter = ref 0
    ; I.unfocusCounter = ref 0
    ; I.numTailbinds = ref 0 }

  
  module Exp = MkExpEvaluator(I)

  let tail_bind_hook : (proc_local -> unit) ref = ref (fun _ -> ())

  (* env  -- The functional environment
     senv -- The shared/replicable environment
     cenv -- The linear environment
     pin  -- The actual process to evaluate *)
  let rec eval_proc (env:value SM.t) (senv: shrsrc CM.t) (cenv:channel CM.t) (pin:proc)
        (state : proc_local) =
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
        if !eval_trace_flag then I.log state.I.id (loc2str (locP pin)^" "^s) else ()
    in let waitone c = 
             if I.is_Term (I.read_comm state c)
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
    I.write_comm state (chanfind "close" c) (I.mkTerm ());
    I.procExit state
  | Exit _ -> eval_trace "detached exit";  I.procExit state
  | Register (_,n,c,p) -> I.register (snd n) (chanfind "register" c);
                          eval_proc env senv cenv p state
  | Service (_,c,n,p) -> eval_proc env senv (CM.add cenv c (I.request (snd n))) p state
  | Wait (_,c,p) ->
    eval_trace "wait";
    waitone (chanfind "wait" c);
    eval_proc env senv cenv p state
  | OutputD (i,c,e,p) -> 
    let v = Exp.eval_exp e env
    in eval_trace ("output "^string_of_value v);
       I.write_comm state (chanfind "OutputD" c) (I.valComm v);
       eval_proc env senv cenv p state
  | InputD (i,x,c,p) ->
    (match I.getVal (I.read_comm state (chanfind "InputD" c)) with
    | Some (Boxed (t,v)) -> 
      eval_trace ("input "^string_of_value v);
      eval_proc (SM.add env (snd x) v) senv cenv p state
    | Some v -> 
      if !dynchecks_flag
      then errr (fst x) " received unboxed data. BUG."
      else eval_trace ("input "^string_of_value v);
           eval_proc (SM.add env (snd x) v) senv cenv p state
    | None -> errr (fst x) " found non-value. BUG.")
  | TailBind (_,c,e,cs) ->
    Thread.yield ();
    !tail_bind_hook state;
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
      in eval_proc env' senv' cenv' p state
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
      let ch = I.spawnRemote env' senv' cenv' p' c' (childState state)
      in eval_proc env senv (CM.add cenv c ch) p state
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
                                                 (childState state)
      in eval_proc env senv (CM.add cenv c ch) p state
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
      in eval_proc env (CM.add senv u (ShrSrc (c',p',env,senv'))) cenv p state
    | MonV (None,_,_,_) -> errr (locE e) " BUG. Shared bind of detatched monad"
    | _ -> errr (locE e) " bind of non-monad. BUG.")
  | Bind _ -> failwith "eval_proc -Wall fix, prior patterns have guards"
  | OutputC (i,c,d,pd,p) ->
    eval_trace "outputC";
    let ch = I.spawn env senv cenv pd d (childState state)
    in I.write_comm state (chanfind "OutputC" c) (I.chanComm ch);
       eval_proc env senv cenv p state
  | InputC (i,disambig,cx,cc,p) ->
    (match !disambig with
    | `Tensor -> 
      eval_trace "inputC";
      (match I.getChan (I.read_comm state (chanfind "InputC" cc)) with
      | Some ch -> eval_proc env senv (CM.add cenv cx ch) p state
      | None -> errr (fst cc) " found non-Chan. BUG.")
    | `DwCastL -> 
      eval_trace "ShftDwL";
      if var2mode cx = Intuist
      then (match I.getVal (I.read_comm state (chanfind "DwCastL" cc)) with
           | Some (Shared s) -> eval_proc env (CM.add senv cx s) cenv p state
           | Some _ | None -> errr (fst cc) "non-Shr in ShftDwL. BUG.")
      else (match I.getChan (I.read_comm state (chanfind "ShftDwnL" cc)) with
           | Some ch -> eval_proc env senv (CM.add cenv cx ch) p state
           | None -> errr (fst cc) " found non-Chan. BUG.")
    | `UpCastR -> 
      eval_trace "UpCastR";
      if var2mode cc = Intuist
      then (* Warning this assumes that the provider channel was set correctly *)
           eval_proc env senv cenv p state
      else (match I.getChan (I.read_comm state (chanfind "UpcastR" cc)) with
           | Some ch -> eval_proc env senv (CM.add cenv cx ch) p state
           | None -> errr (fst cc) " found non-Chan. BUG."))
  | External (i,c,ps) ->
    if LM.is_empty ps
    then errr (i.astloc) "Empty Case Abort"
    else (match I.getLab (I.read_comm state (chanfind "External" c)) with
         | Some l -> if not (LM.mem ps l)
                    then errr (i.astloc) ("External choice, no branch for "
                                          ^string_of_label l^" BUG.")
                    else eval_trace ("external "^string_of_label l);
                         eval_proc env senv cenv (LM.find_exn ps l) state
         | None -> errr (fst c) "non-label in External. BUG.")
  | Internal (_,c,l,p) ->
    eval_trace ("internal "^string_of_label l);
    I.write_comm state (chanfind "Internal" c) (I.labComm l);
    eval_proc env senv cenv p state
  | Fwd (_,c,d) ->
    eval_trace "forward";
    I.forward state (chanfind "Forward" c) (chanfind "Forward" d)
  | InputTy (_,_,c,p) ->
    eval_trace "inputTy";
    (match I.getLab (I.read_comm state (chanfind "InputTy" c)) with
    | Some (_,"_FakeTy_") -> eval_proc env senv cenv p state
    | _ -> errr (fst c) "BUG. Found wrong message for inputTy")
  | OutputTy (_,c,_,p) ->
    eval_trace "outputTy";
    I.write_comm state (chanfind "OutputTy" c) (I.labComm (nullloc,"_FakeTy_"));
    eval_proc env senv cenv p state
  | ShftUpL (_,c1,c2,p) -> (* n.b., c2 records modality already *)
    eval_trace "ShftUpL";
    if var2mode c2 = Intuist
    then let ShrSrc (d,dp,env',senv') = shrfind c2
         in let ch = I.spawn env' senv' CM.empty dp d (childState state);
            in eval_proc env senv (CM.add cenv c1 ch) p state
    else let (ch,ch') = I.newChan ()
         in I.write_comm state (chanfind "UpcastL" c2) (I.chanComm ch);
            eval_proc env senv (CM.add cenv c1 ch') p state
  | ShftDwR (_,c1,c2,p) ->
    eval_trace "ShftDwR";
    if var2mode c2 = Intuist
    then (match p with
         | InputC (_,ambig,c3,c4,p') when !ambig = `UpCastR ->
           I.write_comm state (chanfind "ShftDwR" c1) (I.valComm (Shared (ShrSrc (c3,p',env,senv))))
         | _ -> errr (locP pin) "BUG ShftDwR unrestricted p' problems")
    else let ch = I.spawn env senv cenv p c2 (childState state)
         in I.write_comm state (chanfind "ShftDwR" c1) (I.chanComm ch)

  let rec eval_top (esin:toplvl list) : unit =
    match esin with
    | [] -> Pervasives.exit 0
    | TopLet (f,_,e)::es -> clearmaps ();
                            let v = Exp.eval_exp e (SM.add !topenv (snd f) (Recvar(snd f,e,SM.empty)))
                            in topenv := SM.add !topenv (snd f) v;
                               eval_top es 
    | TopProc (ch,p)::es -> clearmaps ();
                            let state = newstate () in 
                            let chan = I.spawn !topenv CM.empty CM.empty p ch state
                            in if I.is_Term (I.read_comm state chan)
                               then eval_top es
                               else I.abort "Got non-Term at top-proc. BUG."
    | Pass::es -> eval_top es
    | ServDecl _::es -> eval_top es
    | MTypeDecl _::es -> eval_top es
    | STypeDecl _::es -> eval_top es
end
