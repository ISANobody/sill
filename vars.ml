open Base
open Core.Std


(* Variables are shared between all phases, so dependencies make this easier to split off *)

type fvar_raw = string with sexp, bin_io
type fvar = (srcloc * fvar_raw) with sexp, bin_io
let fvar_eq ((_,f1):fvar) ((_,f2):fvar) = f1 = f2
module FS = Set.Make(
  struct
    let compare (_,a) (_,b) = Pervasives.compare a b
    type t = fvar
    let t_of_sexp = fvar_of_sexp
    let sexp_of_t = sexp_of_fvar
  end)
module FM = Core.Std.Map.Make(
  struct
    type t = fvar
    let compare (_,a) (_,b) = Pervasives.compare a b
    let t_of_sexp = fvar_of_sexp
    let sexp_of_t = sexp_of_fvar
  end)
let string_of_fvar ((_,f):fvar) = f
let fm2sm (m : 'a FM.t) : 'a SM.t = 
  SM.of_alist_exn (List.map (FM.to_alist m) (fun (f,x) -> (string_of_fvar f,x)))

type cvar_raw = Shr of string | Lin of string 
              | Aff of string with sexp, bin_io
type cvar = (srcloc * cvar_raw) with sexp, bin_io
let cvar_eq ((_,c1):cvar) ((_,c2):cvar) = c1 = c2
module CS = Set.Make_binable(
  struct
    let compare (_,a) (_,b) = Pervasives.compare a b
    type t = cvar
    let t_of_sexp = cvar_of_sexp
    let sexp_of_t = sexp_of_cvar
    let bin_writer_t = bin_writer_cvar
    let bin_write_t = bin_write_cvar
    let bin_size_t = bin_size_cvar
    let bin_reader_t = bin_reader_cvar
    let __bin_read_t__ = __bin_read_cvar__
    let bin_read_t = bin_read_cvar
    let bin_t = bin_cvar
  end)
module CM = Core.Std.Map.Make_binable(
  struct
    type t = cvar
    let compare (_,a) (_,b) = Pervasives.compare a b
    let t_of_sexp = cvar_of_sexp
    let sexp_of_t = sexp_of_cvar
    let bin_writer_t = bin_writer_cvar
    let bin_write_t = bin_write_cvar
    let bin_size_t = bin_size_cvar
    let bin_reader_t = bin_reader_cvar
    let __bin_read_t__ = __bin_read_cvar__
    let bin_read_t = bin_read_cvar
    let bin_t = bin_cvar
  end)
let string_of_cvar (c:cvar) : string = 
  match c with
  | (_,Lin x) -> "'"^x
  | (_,Shr x) -> "!"^x
  | (_,Aff x) -> "@"^x

let is_lin (c:cvar) : bool =
  match c with
  | (_,Lin _) -> true
  | _ -> false

let is_aff (c:cvar) : bool =
  match c with
  | (_,Aff _) -> true
  | _ -> false

let is_shr (c:cvar) : bool =
  match c with
  | (_,Shr _) -> true
  | _ -> false

let cs_to_string (cs:CS.t) : string = 
  "{"^intercal string_of_cvar ", " (CS.to_list cs)^"}"

let var2mode c : modality =
   match c with
   | (_,Lin _) -> Linear
   | (_,Aff _) -> Affine
   | (_,Shr _) -> Intuist
