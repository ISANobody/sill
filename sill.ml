open Types.Dest (* Needed to initiate the prelude *)
open Base
open Core.Std
open Command
open Command.Spec
open Desugar

let main =
  let spec = (empty +> Spec.flag "backend" ~doc:"thread|fork|ssh select the interpreter to use" (optional_with_default "thread" string)
           +> flag "evaltrace" ~doc:" enable interpretation tracing" no_arg
           +> flag "liveeval" ~doc:" enable forceful interpretation tracing" no_arg
           +> flag "typetrace" ~doc:" enable type tracing" no_arg
           +> flag "subtypetrace" ~doc:" enable subtyping tracing" no_arg
           +> flag "unifytrace"   ~doc:" enable unification tracing" no_arg
           +> flag "interpstats" ~doc:" enable statistics gathering" no_arg
           +> flag "dynchecks" ~doc:" enable dynamic type checking" no_arg
           +> flag "parseonly" ~doc:" stop after parsing" no_arg
           +> flag "strict-polarity" ~doc:" do not insert implicit shifts" no_arg
           +> Spec.flag "gkind" ~doc:"linear|one_weaken|affine select global channel kind"
                                (optional_with_default "linear" string)
           +> (anon ("<program>" %: file)))
  and realMain (backend:string) (eval_trace:bool) (live_trace:bool) (infer_trace:bool) (sub_trace:bool) 
               (unif_trace:bool) (stats:bool) (dyncheck:bool) (parseonly:bool) 
               (polarity:bool)
               (gkind:string) (prog:string)  () = 
      eval_trace_flag := eval_trace;
      live_trace_flag := live_trace;
      infer_trace_flag := infer_trace;
      subtype_trace_flag := sub_trace;
      unify_trace_flag := unif_trace;
      stats_flag := stats;
      dynchecks_flag := dyncheck;
      backend_choice := backend;
      polarity_flag := polarity;
      global_channel_kind := gkind;
      reinit();
      let p = Newparser.main prog
      in if parseonly
         then ()
         else
         let pds = List.concat_map p Desugar.desugarTop in
         Bidir.toplevel pds;
         match !backend_choice with
         | "thread" -> Eval_thread.Impl_Thread.init();
                       Eval_thread.Thread_Eval.eval_top SM.empty pds
         | "fork" -> Eval_pipe.Impl_Pipe.init();
                     Eval_pipe.Pipe_Eval.eval_top SM.empty pds
         | "ssh" -> Eval_ssh.Impl_SSH.init();
                    Eval_ssh.SSH_Eval.eval_top SM.empty pds
         | _ -> prerr_endline "Unknown backend option"
  in run ~version:"1.2.1" (basic ~summary:"SILL interpreter" spec realMain)
