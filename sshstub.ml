open Base
open Core.Std
open Vars
open Eval_ssh

let main : unit =
  eval_trace_flag := realIn stdin bin_reader_bool;
  backend_choice := realIn stdin bin_reader_string;
  Types.Dest.conArities := realIn stdin (SM.bin_reader_t bin_reader_int);
  ancestors := realIn stdin (List.bin_reader_t bin_reader_int);
  let env = realIn stdin (SM.bin_reader_t Value.bin_reader_value)
  and senv = realIn stdin (CM.bin_reader_t Value.bin_reader_shrsrc)
  and cenv = realIn stdin (CM.bin_reader_t bin_reader_int)
  and p = realIn stdin Syntax.Core.bin_reader_proc
  in SSH_Eval.eval_proc env senv (Impl_SSH.unsanitieze_chans cenv) p
