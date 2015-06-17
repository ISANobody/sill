(* Debugging flags *)
let infer_trace_flag : bool ref = ref false
let unify_trace_flag : bool ref = ref false
let subtype_trace_flag : bool ref = ref false
let eval_trace_flag : bool ref = ref false
let live_trace_flag : bool ref = ref false
let bidirectional_flag : bool ref = ref false
let stats_flag : bool ref = ref false
let dynchecks_flag : bool ref = ref false
let global_channel_kind : string ref = ref "linear"
let backend_choice : string ref = ref "none?!"
let polarity_flag : bool ref = ref false
let wall_flag : bool ref = ref false

module SM = Core.Std.Map.Make_binable(Core.Std.String)
module SS = Core.Std.Set.Make_binable(Core.Std.String) 

(* Get around the Jane St warning *)
let physeq x y = x == y

(* We use a list here because it has a way to do pointer equality
   base membership. *)
(* l1 - l2 by == *)
let diffq l1 l2 = List.filter (fun e -> not (List.memq e l2)) l1

let rec uniq (l:'a list) : 'a list=
 match l with
 | [] -> []
 | x::xs -> x :: uniq (List.filter (fun e -> not (x = e)) xs)

(* remove duplicates from physical "sets" *)
let rec uniqq (l : 'a list) : 'a list =
 match l with
 | [] -> []
 | x::xs -> x :: uniqq (List.filter (fun e -> not (x == e)) xs)
            
let rec memq (e:'a) (l : 'a list) : bool =
  match l with
  | [] -> false
  | x::xs -> x == e || memq e xs

let rec pairmemq ((a,b): 'a * 'b) (l : ('a * 'b) list) : bool =
  match l with
  | [] -> false
  | (c,d)::ls -> (a == c && b == d) || pairmemq (a,b) ls

let rec ass_memq (e:'a) (l : ('a*'b) list) : bool =
  match l with
  | [] -> false
  | (x,_)::xs -> x == e || ass_memq e xs

let rec assq (e:'a) (l : ('a*'b) list) : 'b =
  match l with
  | [] -> failwith "assq: not found"
  | (x,y)::xs -> if x == e
                 then y
                 else assq e xs

let rec ass_removeq (e:'a) (l : ('a*'b) list) : ('a*'b) list =
  List.filter (fun (x,_) -> not (x == e)) l

(* post increment operator *)
let post (r : int ref) : int = let i = !r in r := i+1; i

let rec intercal (f : 'a -> string) (sep : string) (l : 'a list) : string =
  match l with
  | [] -> ""
  | [x] -> f x
  | x::xs -> f x ^ sep ^ intercal f sep xs

let intersperse = intercal (fun x -> x)

(* Convert integers to variable strings. 
   Should this be parametric over a list of characters? *)
let rec varstr_of_int (n : int) : string =
 if (0 <= n) && (n <=25)
 then String.make 1 (char_of_int (n+97))
 else (varstr_of_int (n-26)) ^ (String.make 1 (char_of_int (97+(n mod 26))))

(* Removes the first e from l equating with f*)
let rec remove_first_wrt (e:'a) (l:'a list) (f:('a -> 'b)) : 'a list =
  match l with
  | [] -> []
  | x::xs -> if f x = f e
             then xs
             else remove_first_wrt e xs f

let rec mem_wrt (e : 'a) (l:'a list) (f:('a -> 'b)) : bool =
  match l with
  | [] -> false
  | x::xs -> if f x = f e
             then true
             else  mem_wrt e xs f

(* Removes all es from l *)
let remove_all_wrt (es : 'a list) (l : 'a list) (f:('a -> 'b)) : 'a list =
  List.filter (fun x -> not (mem_wrt x es f)) l

(* Dependency circularity means these need to be here instead of lex.mll *)
open Core.Std
type srcloc = Known of int * int | Unknown with sexp, bin_io

let loc2str : srcloc -> string = function
  | Unknown -> "???"
  | Known (l,c) -> "@"^string_of_int l^":"^string_of_int c

let errr (loc:srcloc) (s:string) : 'a =
  prerr_endline ((loc2str loc)^" "^s);
  Pervasives.exit 1

type label_raw = string with sexp, bin_io
type label = (srcloc * label_raw) with sexp, bin_io
let label_eq ((_,l1):label) ((_,l2):label) : bool = l1 = l2
module LM = Core.Std.Map.Make_binable(
  struct
    type t = label
    let compare (_,a) (_,b) = Pervasives.compare a b
    let t_of_sexp = label_of_sexp
    let sexp_of_t = sexp_of_label
    let bin_writer_t = bin_writer_label
    let bin_write_t = bin_write_label
    let bin_size_t = bin_size_label
    let bin_reader_t = bin_reader_label
    let __bin_read_t__ = __bin_read_label__
    let bin_read_t = bin_read_label
    let bin_t = bin_label
  end)
let lmIter2 (m1:'a LM.t) (m2:'b LM.t) (f:(key:label -> data:[ `Both of 'a * 'b | `Left of 'a | `Right of 'b ]
-> unit)) : unit =
  let _ = LM.merge m1 m2 (fun ~key:k d -> f k d; None)
  in ()
let stripNullPadding (s:string) : string =
  Core.Std.String.concat_map s (fun x -> match Core.Std.Char.to_int x with
                                         | 0 -> ""
                                         | _ -> Core.Std.String.make 1 x)
let string_of_label ((_,l):label) = l

let rec filter_map2_exn (l1:'a list) (l2:'b list) (f:'a -> 'b -> 'c option) : 'c list =
  match l1,l2 with
  | [],[] -> []
  | _,[] -> failwith "filter_map2_exn length1"
  | [],_ -> failwith "filter_map2_exn length2"
  | (x::xs),(y::ys) -> match f x y with
                       | Some z -> z :: (filter_map2_exn xs ys f)
                       | None -> filter_map2_exn xs ys f

let fresh_counter = ref 0
let priv_name () = "$"^string_of_int (post fresh_counter)

(* This is in Core.Std.Mutex, but doesn't work for me *)
let crit (m:Core.Std.Mutex.t) (f:unit -> 'a) : 'a =
  Core.Std.Mutex.lock m;
  let r = f ()
  in Core.Std.Mutex.unlock m;
     r

(* Modalities: Intuistionistic/Affine/Linear I don't know if this is the best module *)

type modality = Linear | Affine | Intuist with sexp, bin_io
let modetag m : string = match m with
                       | Affine  -> "@"
                       | Linear  -> "'"
                       | Intuist -> "!"
let string_of_mode m : string = match m with
                              | Affine -> "affine"
                              | Linear -> "linear"
                              | Intuist -> "shared"

(* TODO Maybe this should go in vars.ml instead? *)
(* TODO Channels record modality too. Why not combine them? *)
type tyvar = modality * string with sexp, bin_io
let string_of_tyvar (m,x) = modetag m ^ x
module TS = Set.Make(
  struct
    type t = tyvar
    let compare x1 x2 = Pervasives.compare x1 x2
    let t_of_sexp = tyvar_of_sexp
    let sexp_of_t = sexp_of_tyvar
  end)
module TM = Map.Make(
  struct
    type t = tyvar
    let compare x1 x2 = Pervasives.compare x1 x2
    let t_of_sexp = tyvar_of_sexp
    let sexp_of_t = sexp_of_tyvar
  end)
let sessionQs : [`M of string | `S of tyvar] list SM.t ref = ref SM.empty
