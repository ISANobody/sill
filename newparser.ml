open Base
open Core.Std
open MParser
open MParser.Tokens
open Vars
open Fullsyntax

let keywords = ["fun"; "and"; "if"; "then"; "else"; "forall"; "exists"
               ;"let"; "in"; "send"; "recv"; "case"; "of"; "wait"
               ;"close"; "abort"]

(* This is pretty ugly. The correct way to handle arbitrary paired comments is to treat
   eat them while consume spare white space. Of course, this isn't actually modularized
   so we need to rebind 'spaces' and some functions from MParser that use it. Ugh. *)

let rec comment_go_ : (unit,'s) MParser.t Lazy.t = lazy(
  (skip_many_until skip_any_char_or_nl (attempt (skip_symbol "*)")
                             <|>
                             (perform
                               attempt (skip_string "(*");
                               Lazy.force comment_go_;
                               Lazy.force comment_go_)))
  <?> ""
)
and comment_ = lazy((skip_string "(*" >> Lazy.force comment_go_) <?> "")
let comment = Lazy.force comment_
let spaces = MParser.spaces >> skip_many comment

(* BEGIN COPIED STUFF *)
let symbol s = skip_string s >> spaces >> return s
let skip_symbol s = skip_string s >> spaces
let char_sp c = char c >> spaces >> return c

let escaped_char s =
  (any_of "nrtb\\\"\'" |>>
       (function
          | 'n' -> '\n'
          | 'r' -> '\r'
          | 't' -> '\t'
          | 'b' -> '\b'
          | c   -> c)) s

let escape_sequence_dec =
  let int_of_dec c =
    (Char.to_int c) - (Char.to_int '0') in
  let char_of_digits d2 d1 d0 =
    char_of_int (100 * (int_of_dec d2) + 10 * (int_of_dec d1)
                 + (int_of_dec d0))
  in
    fun s ->
      (digit >>= fun d2 ->
       digit >>= fun d1 ->
       digit >>= fun d0 ->
       try_return3 char_of_digits d2 d1 d0
         "Escape sequence is no valid character code" s) s

let escape_sequence_hex =
  let int_of_hex c =
    if      '0' <= c && c <= '9' then (Char.to_int c) - (Char.to_int '0')
    else if 'a' <= c && c <= 'f' then (Char.to_int c) - (Char.to_int 'a') + 10
    else if 'A' <= c && c <= 'F' then (Char.to_int c) - (Char.to_int 'A') + 10
    else failwith "MParser.int_of_hex: no hex digit" in
  let char_of_digits h1 h0 =
    char_of_int (16 * (int_of_hex h1) + (int_of_hex h0))
  in
    fun s ->
      (char 'x'  >>
       hex_digit >>= fun h1 ->
       hex_digit >>= fun h0 ->
       try_return2 char_of_digits h1 h0
         "Escape sequence is no valid character code" s) s

let escape_sequence s =
     (escape_sequence_dec
  <|> escape_sequence_hex) s

let char_token s =
       ((char '\\' >> (escaped_char <|> escape_sequence))
    <|>  any_char) s

let string_literal s =
    (char '"' >> (many_chars_until char_token (char_sp '"'))
     <?> "string literal") s

let integer s =
    (regexp (make_regexp "\\d+") >>= fun digits ->
     spaces           >>
     try_return int_of_string digits "Integer value out of range" s
     <?> "integer value") s

let float_tok s =
     (regexp (make_regexp "-?\\d+\\.(\\d*)?((e|E)?(\\+|-)?\\d+)?") >>= fun digits ->
     spaces         >>
     try_return Float.of_string digits "Not a valid float value" s
     <?> "float value") s

(* END OF COPIED JUNK *)

(* TODO Why is this here? It's from parse.mly but needs a better long term home *)
let chan2tyvar (c:cvar) : tyvar =
  match c with
  | (_,Lin x) -> (Linear,x)
  | (_,Aff x) -> (Affine,x)
  | (_,Shr x) -> (Intuist,x)

(* Because OCaml isn't lazy by default, we'll need to do some knot-tying via OCaml's
   Lazy module. This means that several of the combinators need lazy variants. :/ *)

let rec sep_by1_lazy sep (p : ('a,'s) MParser.t Lazy.t) : ('a list,'s) MParser.t =
  perform
    x <-- Lazy.force p;
    xs <-- many (sep >> Lazy.force p);
    return (x::xs)

let sep_by_lazy sep p =
  sep_by1_lazy sep p <|> return []

let between_lazy left right (p : ('a,'s) MParser.t Lazy.t) : ('a,'s) MParser.t =
  perform
    skip_char left;
    _ <-- spaces;
    ret <-- Lazy.force p;
    skip_char right;
    _ <-- spaces;
    return ret

let parens_lazy p = between_lazy '(' ')' p

(* END LAZY DUPLICATES *)

(* Since there was an earlier ocamllex/ocamlyacc version of this we need to convert
   between MParser's notion of a location and the one that the rest of SILL uses.
   TODO remove this conversion.
   TODO provide positional spans and not just start points for srclocs. *)

let getSloc =
  perform
    (_,l,c) <-- get_pos;
    return ({lnum = l; cnum = c})

(* We allow one case where identifiers cannot be followed by spaces: branch selection.
   As a result some of these identifier parsers will have id_ versions that do not consume
   trailing spaces. *)

let id_lower_ : (fvar,'s) MParser.t =
  attempt (perform
    sloc <-- getSloc;
    c <-- lowercase;
    cs <-- many_chars (alphanum <|> char '_' <|> char ''');
    let name = ((String.make 1 c) ^ cs)
    in if List.mem keywords name
       then zero
       else return (sloc,name))
  <?> "lowercase identifier"

let id_lower = id_lower_ >>= fun s -> spaces >> return s

let id_upper_ : (fvar,'s) MParser.t =
  attempt (perform
    sloc <-- getSloc;
    c <-- uppercase;
    cs <-- many_chars (alphanum <|> char '_' <|> char ''');
    let name = ((String.make 1 c) ^ cs)
    in if List.mem keywords name
       then zero
       else return (sloc,name))
  <?> "uppercase identifier"

let id_upper = id_upper_ >>= fun s -> spaces >> return s

let patvar : (fvar,'s) MParser.t = 
  id_lower 
  <|>
  (perform
    sloc <-- getSloc;
    skip_symbol "_";
    return (sloc,"_"))
  <?> "pattern variable"

let id_lin_ : (cvar,'s) MParser.t =
  (perform
    sloc <-- getSloc;
    skip_char ''';
    x <-- id_lower_;
    return (sloc,Lin (snd x)))

let id_lin = id_lin_ >>= fun s -> spaces >> return s

let id_aff_ : (cvar,'s) MParser.t =
  (perform
    sloc <-- getSloc;
    skip_char '@';
    x <-- id_lower_;
    return (sloc,Aff (snd x)))

let id_aff = id_aff_ >>= fun s -> spaces >> return s

let id_shr_ : (cvar,'s) MParser.t =
  (perform
    sloc <-- getSloc;
    skip_char '!';
    x <-- id_lower_;
    return (sloc,Shr (snd x)))

let id_shr = id_shr_ >>= fun s -> spaces >> return s

let linchan = id_lin <?> "linear channel"
let affchan = id_aff <?> "affine channel"
let shrchan = id_shr <?> "unrestricted channel"
let subchan = id_lin <|> id_aff <?> "substructural channel"
let anychan_ = id_lin_ <|> id_aff_ <|> id_shr_ <?> "channel"
let anychan = id_lin <|> id_aff <|> id_shr <?> "channel"
let sesvar  = (id_lin <|> id_aff <|> id_shr <?> "session type variable") |>> chan2tyvar
let datavar = id_lower <?> "data-level type variable"
let quant   = (sesvar |>> fun x -> `S x) <|> (datavar |>> fun x -> `M (snd x))
            <?> "quantifier"

let rec tyapp_ : (tyapp,'s) MParser.t Lazy.t = lazy (
  perform
    name <-- id_upper;
    args <-- many (  (id_upper |>> (fun x -> (`A x)))
                 <|> (attempt (Lazy.force mtype_atom_) |>> (fun x -> `M x))
                 <|> (attempt (Lazy.force stype_atom_) |>> (fun x -> `S x))
                 <?> "data-level or session type");
    return (TyApp (name,args))
)
and mtype_atom_ : (mtype,'s) MParser.t Lazy.t = lazy(
  (perform
    (_,x) <-- datavar;
    return (MVar x))
  <|>
  (perform
    (_,x) <-- id_upper;
    return (Comp (x,[])))
  <|>
  (skip_symbol "()" >> return (Comp ("()",[])))
  <|>
  (perform
    skip_symbol "[";
    t <-- Lazy.force mtype_;
    skip_symbol "]";
    return (Comp ("[]",[`M t])))
  <|>
  (perform
     skip_symbol "{";
     (skip_symbol "}" >> return (MonT(None,[])))
     <|>
     (perform
       t <-- Lazy.force stype_;
       (skip_symbol "}" >> return (MonT(Some t,[])))
       <|>
       (perform
         skip_symbol "<-";
         ts <-- sep_by1_lazy (skip_symbol ";") stype_;
         skip_symbol "}";
         return (MonT(Some t,ts)))))
  <|>
  (perform
    skip_symbol "(";
    t1 <-- Lazy.force mtype_;
    (perform
       skip_symbol ",";
       t2 <-- Lazy.force mtype_;
       skip_symbol ")";
       return (Comp(",",[`M t1;`M t2])))
    <|>
     (skip_symbol ")" >> return t1))
  <?> "data-level type"
)
and mtype_basic_ : (mtype,'s) MParser.t Lazy.t = lazy(
   attempt (Lazy.force tyapp_ |>> tyapp2mtype)
   <|>
   Lazy.force mtype_atom_
  <?> "data-level type"
)
and mtype_ : (mtype,'s) MParser.t Lazy.t = lazy(
  (perform
     t1 <-- Lazy.force mtype_basic_;
     arr <-- try_skip (skip_symbol "->");
     if arr
     then perform
            t2 <-- Lazy.force mtype_;
            return (Comp("->",[`M t1;`M t2]))
     else return t1)
  <?> "data-level type"
)
and stype_ : (stype,'s) MParser.t Lazy.t = lazy(
  (perform
     attempt (skip_char '!' >> not_followed_by lowercase "" >> spaces);
     t <-- Lazy.force stype_;
     return (Bang t))
  <|>
  (perform
     attempt (skip_char '@' >> not_followed_by lowercase "" >> spaces);
     t <-- Lazy.force stype_;
     return (TyAt t))
  <|>
  (perform
     attempt (skip_char ''' >> not_followed_by lowercase "" >> spaces);
     t <-- Lazy.force stype_;
     return (Prime t))
  <|>
  attempt (perform
     m <-- Lazy.force mtype_;
     (perform
        skip_symbol "/\\";
        s <-- Lazy.force stype_;
        return (TyOutD (Linear,m,s)))
     <|>
     (perform
        skip_symbol "=>";
        s <-- Lazy.force stype_;
        return (TyInD (Linear,m,s))))
  <|>
  (perform
    skip_symbol "forall";
    q <-- sesvar;
    skip_symbol ".";
    s <-- Lazy.force stype_;
    return (Forall (Linear,q,s)))
  <|>
  (perform
    skip_symbol "exists";
    q <-- sesvar;
    skip_symbol ".";
    s <-- Lazy.force stype_;
    return (Exists (Linear,q,s)))
  <|>
  Lazy.force stype_times_
  <?> "session type"
)
and stype_times_ : (stype,'s) MParser.t Lazy.t = lazy(
  (perform
    s1 <-- Lazy.force stype_basic_;
    (perform 
      skip_symbol "*";
      s2 <-- Lazy.force stype_;
      return (TyOutC (Linear,s1,s2)))
    <|>
    (perform 
      skip_symbol "-o";
      s2 <-- Lazy.force stype_;
      return (TyInC (Linear,s1,s2)))
    <|>
    (return s1))
  <?> "session type"
)
and stype_basic_ : (stype,'s) MParser.t Lazy.t = lazy(
  Lazy.force tyapp_ |>> tyapp2stype
  <|>
  Lazy.force stype_atom_
  <?> "session type"
)
and stype_atom_ : (stype,'s) MParser.t Lazy.t = lazy(fun s ->
  ((perform
    l <-- getSloc;
    x <-- sesvar;
    return (SVar (l,x)))
  <|>
  (perform
    (l,x) <-- id_upper;
    return (SComp (l,x,[])))
  <|>
  (perform
     skip_symbol "1";
     return (Stop Linear))
  <|>
  (perform
    skip_symbol "+{";
    ts <-- sep_by ((fun s -> (perform
                     label <-- id_lower;
                     skip_symbol ":"; 
                     t <-- Lazy.force stype_;
                     return (label,(s,t))) s)
                    <?> "mapping from label to session type (e.g., foo:1)")
                  (skip_symbol ";");
    skip_symbol "}";
    match LM.of_alist ts with
    | `Ok m -> return (Intern (Linear,LM.map m snd))
    | `Duplicate_key l -> 
        let (s,_) = List.Assoc.find_exn ts l
        in fun _ -> Consumed_failed (unexpected_error s ("duplicate label "^snd l)))
  <|>
  (perform
    skip_symbol "&{";
    ts <-- sep_by ((fun s -> (perform
                     label <-- id_lower;
                     skip_symbol ":"; 
                     t <-- Lazy.force stype_;
                     return (label,(s,t))) s)
                    <?> "mapping from label to session type (e.g., foo:1)")
                  (skip_symbol ";");
    skip_symbol "}";
    match LM.of_alist ts with
    | `Ok m -> return (Extern (Linear,LM.map m snd))
    | `Duplicate_key l -> 
        let (s,_) = List.Assoc.find_exn ts l
        in fun _ -> Consumed_failed (unexpected_error s ("duplicate label "^snd l)))
  <|>
  parens_lazy stype_
  <?> "session type") s
)

let mtype = Lazy.force mtype_
let mtype_atom = Lazy.force mtype_atom_
let stype = Lazy.force stype_
let tyapp = Lazy.force tyapp_

let constructor =
  perform
    name <-- id_upper;
    args <-- many mtype_atom;
    return (snd name,args)
  
let mtypedec : (toplvl,'s) MParser.t =
  (perform
    sloc <-- getSloc;
    skip_symbol "type";
    id <-- id_upper;
    qs <-- many quant;
    skip_symbol "=";
    ts <-- sep_by constructor (skip_symbol "|");
    skip_symbol ";;";
    match SM.of_alist ts with
    | `Ok m -> return (MTypeDecl (id,qs,m))
    | `Duplicate_key k -> errr sloc ("duplicate constructor name "^k))
  <?> "data-level type declaration"

let stypedec : (toplvl,'s) MParser.t =
  (perform
    mode <-- (  (skip_symbol "ltype" >> return Linear)
            <|> (skip_symbol "atype" >> return Affine)
            <|> (skip_symbol "utype" >> return Intuist));
    id <-- id_upper;
    qs <-- many quant;
    skip_symbol "=";
    t <-- stype;
    skip_symbol ";;";
    return (STypeDecl (mode,id,qs,t)))
  <?> "session type declaration"

let data_pattern : ((string * fvar list),'s) MParser.t =
  (perform
    skip_symbol "|";
    (perform
      name <-- id_upper;
      pats <-- many patvar;
      skip_symbol "->";
      return (snd name,pats))
    <|>
    (perform
      skip_symbol "[]";
      skip_symbol "->";
      return ("[]",[]))
    <|>
    (perform
      skip_symbol "(";
      x1 <-- patvar;
      skip_symbol ",";
      x2 <-- patvar;
      skip_symbol ")";
      skip_symbol "->";
      return (",",[x1;x2]))
    <|>
    (perform
      x1 <-- patvar;
      skip_symbol "::";
      x2 <-- patvar;
      skip_symbol "->";
      return ("::",[x1;x2]))
    <?> "pattern match")
  <?> "pattern match"

let rec exp_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform 
    sloc <-- getSloc;
    e1 <-- Lazy.force exp_and_;
    (perform
      skip_symbol "||";
      e2 <-- Lazy.force exp_;
      return (Bin (sloc,Or,e1,e2)))
    <|>
    (return e1))
  <?> "expression"
)
and exp_and_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform
    sloc <-- getSloc;
    e1 <-- Lazy.force exp_eq_;
    (perform
      skip_symbol "&&";
      e2 <-- Lazy.force exp_and_;
      return (Bin (sloc,And,e1,e2)))
    <|>
    (return e1))
)
and exp_eq_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform
    sloc <-- getSloc;
    e1 <-- Lazy.force exp_compare_;
    (perform
      skip_symbol "=";
      e2 <-- Lazy.force exp_eq_;
      return (Bin (sloc,Eq,e1,e2)))
    <|>
    (return e1))
)
and exp_compare_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform
    sloc <-- getSloc;
    e1 <-- Lazy.force exp_cons_;
    (perform
      skip_symbol "<=";
      e2 <-- Lazy.force exp_eq_;
      return (Bin (sloc,LE,e1,e2)))
    <|>
    (perform
      skip_symbol ">=";
      e2 <-- Lazy.force exp_eq_;
      return (Bin (sloc,GE,e1,e2)))
    <|>
    (perform
      skip_symbol "<";
      e2 <-- Lazy.force exp_eq_;
      return (Bin (sloc,Less,e1,e2)))
    <|>
    (perform
      skip_symbol ">";
      e2 <-- Lazy.force exp_eq_;
      return (Bin (sloc,GT,e1,e2)))
    <|>
    (return e1))
)
and exp_cons_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform
    sloc <-- getSloc;
    e1 <-- Lazy.force exp_add_;
    (perform
      skip_symbol "::";
      e2 <-- Lazy.force exp_;
      return (Sat(sloc,"::",[e1;e2])))
    <|>
    (return e1))
)
and exp_add_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform
    sloc <-- getSloc;
    e1 <-- Lazy.force exp_times_;
    (perform
      skip_symbol "+.";
      e2 <-- Lazy.force exp_;
      return (Bin (sloc,FAdd,e1,e2)))
    <|>
    (perform
      skip_symbol "-.";
      e2 <-- Lazy.force exp_;
      return (Bin (sloc,FSub,e1,e2)))
    <|>
    (perform
      skip_symbol "+";
      e2 <-- Lazy.force exp_;
      return (Bin (sloc,Add,e1,e2)))
    <|>
    (perform
      (attempt (char '-' >> not_followed_by (char '<') "" >> spaces));
      e2 <-- Lazy.force exp_;
      return (Bin (sloc,Sub,e1,e2)))
    <|>
    (perform
      skip_symbol "^";
      e2 <-- Lazy.force exp_;
      return (Bin (sloc,Concat,e1,e2)))
    <|>
    (return e1))
)
and exp_times_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform
    sloc <-- getSloc;
    e1 <-- Lazy.force exp_exp_;
    (perform
      skip_symbol "*.";
      e2 <-- Lazy.force exp_times_;
      return (Bin (sloc,FMul,e1,e2)))
    <|>
    (perform
      skip_symbol "/.";
      e2 <-- Lazy.force exp_times_;
      return (Bin (sloc,FDiv,e1,e2)))
    <|>
    (perform
      skip_symbol "*";
      e2 <-- Lazy.force exp_times_;
      return (Bin (sloc,Mul,e1,e2)))
    <|>
    (perform
      skip_symbol "/";
      e2 <-- Lazy.force exp_times_;
      return (Bin (sloc,Div,e1,e2)))
    <|>
    (return e1))
  <?> "expression"
)
and exp_exp_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform
    sloc <-- getSloc;
    e1 <-- Lazy.force exp_app_;
    (perform
      skip_symbol "**";
      e2 <-- Lazy.force exp_exp_;
      return (Bin (sloc,Exp,e1,e2)))
    <|>
    (return e1))
  <?> "expression"
)
and exp_app_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform
    es <-- many1 (Lazy.force exp_basic_);
    return (List.reduce_exn es ~f:(fun ea e' -> App (locE ea,ea,e'))))
  <?> "expression"
)
and exp_basic_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform
    sloc <-- getSloc;
    skip_symbol "fun";
    (x::xs) <-- many1 patvar;
    skip_symbol "->";
    e <-- Lazy.force exp_;
    return (Fun(sloc,x,xs,e)))
  <|>
  (perform
    sloc <-- getSloc;
    skip_symbol "let";
    name <-- id_lower;
    pats <-- many patvar;
    skip_symbol ":";
    t <-- mtype;
    skip_symbol "=";
    e1 <-- Lazy.force exp_;
    skip_symbol "in";
    e2 <-- Lazy.force exp_;
    return (Let (sloc,`M t,name,pats,e1,e2)))
  <|>
  (perform
    sloc <-- getSloc;
    skip_symbol "if";
    ec <-- Lazy.force exp_;
    skip_symbol "then";
    et <-- Lazy.force exp_;
    skip_symbol "else";
    ef <-- Lazy.force exp_;
    return (If (sloc,ec,et,ef)))
  <|>
  (perform
    sloc <-- getSloc;
    skip_symbol "case";
    e <-- Lazy.force exp_;
    skip_symbol "of";
    es <-- many1 (perform
                   (c,pat) <-- data_pattern;
                   ep <-- Lazy.force exp_;
                   return (c,(pat,ep)));
    match SM.of_alist es with
    | `Ok m -> return (Case (sloc,e,m))
    | `Duplicate_key k -> errr sloc ("duplicate pattern for "^k))
  <|>
  (perform
    sloc <-- getSloc;
    c <-- anychan;
    skip_symbol "<-";
    skip_symbol "{";
    p <-- Lazy.force proc_;
    skip_symbol "}";
    (perform
      skip_symbol "-<";
      cs <-- many anychan;
      return (Monad (sloc,Some c,p,cs)))
    <|>
    (return (Monad (sloc,Some c,p,[]))))
  <|>
  Lazy.force exp_atom_
  <?> "expression"
)
and exp_atom_ : (exp,'s) MParser.t Lazy.t = lazy(
  (perform
    sloc <-- getSloc;
    x <-- id_lower_ <|> id_upper_;
    (perform
      skip_char '<';
      ts <-- (sep_by (  attempt (perform
                                 t <--tyapp;
                                 followed_by (skip_symbol "," <|> skip_char '>') "";
                                 return (`A t))
                   <|> attempt (perform
                                 t <-- stype;
                                 followed_by (skip_symbol "," <|> skip_char '>') "";
                                 return (`S t))
                   <|> attempt (perform
                                 t <-- mtype;
                                 followed_by (skip_symbol "," <|> skip_char '>') "";
                                 return (`M t))) (skip_symbol ",")
             <?> "','-separated lists of types");
      skip_char '>';
      spaces;
      return (PolyApp (sloc,x,ts)))
    <|>
    (spaces >> return (Var (sloc,x))))
  <|>
  (perform
    sloc <-- getSloc;
    x <-- id_upper;
    return (Var (sloc,x)))
  <|>
  attempt (perform
    sloc <-- getSloc;
    f <-- attempt float_tok;
    return (Con (sloc,Float f)))
  <|>
  (perform
    sloc <-- getSloc;
    i <-- attempt integer;
    return (Con (sloc,Int i)))
  <|>
  (perform
    sloc <-- getSloc;
    skip_symbol "()";
    return (Sat(sloc,"()",[])))
  <|>
  (perform
    sloc <-- getSloc;
    s <-- attempt string_literal;
    return (Con (sloc,String s)))
  <|>
  attempt (perform
    sloc <-- getSloc;
    (char '<' >> not_followed_by (  char '=' 
                                <|> char '''
                                <|> char '@'
                                <|> char '!') "" >> spaces);
    e <-- Lazy.force exp_;
    skip_symbol ":";
    t <-- mtype;
    skip_symbol ">";
    return (Cast (sloc,e,t)))
  <|>
  (perform
     skip_symbol "[";
     es <-- sep_by_lazy (skip_symbol ";") exp_;
     skip_symbol "]";
     sloc_end <-- getSloc;
     return (List.fold_right es ~init:(Sat(sloc_end,"[]",[]))
                                ~f:(fun e acc -> Sat(locE e,"::",[e;acc]))))
  <|>
  (perform
     sloc <-- getSloc;
     skip_symbol "(";
     e1 <-- Lazy.force exp_;
     (perform
       skip_symbol ",";
       e2 <-- Lazy.force exp_;
       skip_symbol ")";
       return (Sat(sloc,",",[e1;e2])))
     <|>
     (skip_symbol ")" >> return e1))
  <?> "expression"
)
and proc_inst_ : ((proc option -> proc),'s) MParser.t Lazy.t = lazy(
  (perform
    sloc <-- getSloc;
    skip_symbol "abort";
    return (function
      | None -> Abort sloc
      | Some cont -> errr (locP cont) "'abort' must end its process"))
  <|>
  (perform
    sloc <-- getSloc;
    skip_symbol "if";
    ec <-- Lazy.force exp_;
    skip_symbol "then";
    pt <-- Lazy.force proc_;
    skip_symbol "else";
    pf <-- Lazy.force proc_;
    return (function
      | None -> IfP (sloc,ec,pt,pf)
      | Some p -> errr (locP p) "BUG process if-then-else cannot be followed a process"))
  <|>
  (perform
    sloc <-- getSloc;
    skip_symbol "case";
    (perform
      c <-- subchan;
      skip_symbol "of";
      cases <-- many (perform 
                       skip_symbol "|";
                       l <-- id_lower;
                       skip_symbol "->";
                       p <-- Lazy.force proc_;
                       return (l,p));
      return (function
        | None -> (match LM.of_alist cases with
                  | `Ok m -> External (sloc,c,m)
                  | `Duplicate_key l -> errr (fst l) ("duplicate case for label "^string_of_label l))
        | Some p -> errr (locP p) "BUG external choice cannot be followed a process"))
    <|>
    (perform
      e <-- Lazy.force exp_;
      skip_symbol "of";
      cases <-- many1 (perform
                         (c,pat) <-- data_pattern;
                         p <-- Lazy.force proc_;
                         return (c,(pat,p)));
    return (function
      | None -> (match SM.of_alist cases with
                | `Ok m -> CaseP (sloc,e,m)
                | `Duplicate_key k -> errr sloc ("duplicate pattern for "^k))
      | Some p -> errr (locP p) "BUG process case cannot be followed a process")))
  <|>
  (perform
    sloc <-- getSloc;
    e <-- attempt (Lazy.force exp_);
    return (function
      | Some cont -> Seq(sloc,e,cont)
      | None -> errr sloc "Cannot end a process with a sequencing statement"))
  <|>
  (perform
    sloc <-- getSloc;
    skip_symbol "<";
    x <-- sesvar;
    skip_symbol ">";
    skip_symbol "<-";
    skip_symbol "recv";
    c <-- subchan;
    return (function
      | Some cont -> InTy(sloc,x,c,cont)
      | None -> errr sloc "Cannot end a process by receiving a session type"))
  <|>
  (perform 
    sloc <-- getSloc;
    skip_symbol "close";
    c <-- subchan;
    return (function
      | None -> Close (sloc,c)
      | Some p -> errr (locP p) "Cannot have a process after a close statement"))
  <|>
  (perform 
    sloc <-- getSloc;
    skip_symbol "wait";
    c <-- subchan;
    return (function
      | Some cont -> Wait(sloc,c,cont)
      | None -> errr sloc "Cannot end a process by waiting"))
  <|>
  (perform
    sloc <-- getSloc;
    skip_symbol "let";
    name <-- id_lower;
    pats <-- many patvar;
    skip_symbol ":";
    t <-- mtype;
    skip_symbol "=";
    e <-- Lazy.force exp_;
    return (function
      | Some cont -> LetP (sloc,`M t,name,pats,e,cont)
      | None -> errr sloc "Cannot end a process with a let binding"))
  <|>
  (perform 
    sloc <-- getSloc;
    skip_symbol "send";
    c <-- subchan;
    (perform
      e <-- attempt (Lazy.force exp_);
      return (function
        | Some cont -> OutD(sloc,c,e,cont)
        | None -> errr sloc "Cannot end a process by sending a value"))
    <|>
    (perform
      c' <-- subchan;
      return (function
        | Some cont -> Throw (sloc,c,c',cont)
        | None -> errr sloc "Cannot end a process by sending a channel"))
    <|>
    (perform
      skip_symbol "(";
      c2 <-- anychan;
      skip_symbol "<-";
      p <-- Lazy.force proc_;
      skip_symbol ")";
      return (function
        | Some cont -> OutC (sloc,c,c2,p,cont)
        | None -> ShftDwR (sloc,c,c2,p)))
    <|>
    (perform
      skip_symbol "<";
      t <-- stype;
      skip_symbol ">";
      return (function
        | Some cont -> OutTy (sloc,c,t,cont)
        | None -> errr sloc "Cannot end a process by sending a type"))
  )
  <|>
  (perform
    sloc <-- getSloc;
    x <-- id_lower;
    skip_symbol "<-";
    skip_symbol "recv";
    c <-- subchan;
    return (function
      | Some cont -> InD (sloc,x,c,cont)
      | None -> errr sloc "Cannot end a process by receiving a value"))
  <|>
  (perform
    sloc <-- getSloc;
    skip_symbol "_";
    skip_symbol "<-";
    (perform
      skip_symbol "recv";
      c <-- subchan;
      return (function
        | Some cont -> InD (sloc,(sloc,priv_name ()),c,cont)
        | None -> errr sloc "Cannot end a process by receiving a value"))
    <|>
    (perform
      e <-- Lazy.force exp_;
      (perform
        skip_symbol "-<";
        cs <-- many anychan;
        return (function
          | Some cont -> Detached (sloc,e,cs,cont)
          | None -> errr sloc "Cannot end a process with a monadic bind"))
      <|>
      (return (function
         | Some cont -> Detached (sloc,e,[],cont)
         | None -> errr sloc "Cannot end a process with a monadic bind"))))
  <|>
  (perform
    sloc <-- getSloc;
    c1 <-- anychan_;
    (perform
      skip_char '.';
      l <-- id_lower;
      return (function
        | Some cont -> Internal (sloc,c1,l,cont)
        | None -> errr sloc "Cannot end a process with an internal choice"))
    <|>
    (perform
      spaces;
      skip_symbol "<-";
      (skip_symbol "recv" >>
        (perform
          c2 <-- anychan;
          return (function
            | Some cont -> InC (sloc,c1,c2,cont)
            | None -> errr sloc "Cannot end a process with an internal choice")))
      <|>
      (perform
        c2 <-- subchan;
        return (function
          | None -> Fwd (sloc,c1,c2)
          | Some cont -> errr (locP cont) "Forwarding must end its process"))
      <|>
      (perform
        e <-- Lazy.force exp_;
        (perform
          skip_symbol "-<";
          cs <-- many anychan;
          return (function
            | Some cont -> Bind (sloc,c1,e,cs,cont)
            | None -> TailBind (sloc,c1,e,cs)))
        <|>
        (return (function
           | Some cont -> Bind (sloc,c1,e,[],cont)
           | None -> TailBind (sloc,c1,e,[]))))
      <|>
      (perform
        skip_symbol "send";
        c2 <-- anychan;
        return (function
          | Some cont -> ShftUpL (sloc,c1,c2,cont)
          | None -> errr sloc "Cannot end a process with an upcast")))
  )
  <|>
  (perform
    p <-- parens_lazy proc_;
    return (function
      | None -> p
      | Some cont -> errr (locP cont) "A parenthesised process must be the end of a process"))
  <?> "process statement"
)
and proc_ : (proc,'s) MParser.t Lazy.t = lazy(
  (perform
    pis <-- sep_by1_lazy (attempt (char ';' >> not_followed_by (char ';') "" >> spaces)) proc_inst_;
    (match (List.fold_right pis ~init:None ~f:(fun stmt acc -> Some (stmt acc))) with
    | None -> zero
    | Some p -> return p))
  <?> "process"
)

let exp = Lazy.force exp_
let proc = Lazy.force proc_

let topsig =
  (perform
    name <-- id_lower;
    skip_symbol ":";
    (perform
      skip_symbol "forall";
      qs <-- (perform
        skip_symbol "<";
        qs <-- sep_by quant (skip_symbol ",");
        skip_symbol ">";
        return qs) <?> "quantifier list (e.g., <a,'b,@c>)";
      skip_symbol ".";
      t <-- mtype;
      return (name,`P (Poly (qs,t))))
    <|>
    (perform
      t <-- mtype;
      return (name,`M t)))
  <?> "type signature"

let topdef_ = 
  perform
    t <-- topsig;
    skip_symbol ";;";
    (perform
      name <-- id_lower;
      pats <-- many patvar;
      skip_symbol "=";
      e <-- exp;
      return (name,TopExp (name,t,pats,e)))
    <|>
    (perform
       c <-- anychan;
       skip_symbol "<-";
       name <-- id_lower;
       pats <-- many patvar;
       (perform
         skip_symbol "=";
         p <-- proc;
         return (name,TopMon (name,t,pats,c,p,[])))
       <|>
       (perform
          skip_symbol "-<";
          cs <-- many anychan;
          skip_symbol "=";
          p <-- proc;
          return (name,TopMon (name,t,pats,c,p,cs))))
    <|>
    (perform
       sloc <-- getSloc;
       c <-- skip_symbol "_";
       skip_symbol "<-";
       name <-- id_lower;
       pats <-- many patvar;
       (perform
         skip_symbol "=";
         p <-- proc;
         return (name,TopDet (name,t,pats,sloc,p,[])))
       <|>
       (perform
          skip_symbol "-<";
          cs <-- many anychan;
          skip_symbol "=";
          p <-- proc;
          return (name,TopDet (name,t,pats,sloc,p,cs))))
    <?> ("definition for "^snd (fst t))

let topdef : (toplvl,'s) MParser.t = 
  (perform
    defs <-- sep_by1 topdef_ (skip_symbol "and");
    skip_symbol ";;";
    match FM.of_alist defs with
    | `Ok m -> return (TopLets m)
    | `Duplicate_key k -> errr (fst k) ("duplicate binding for "^string_of_fvar k))
  <?> "top level definition"

let topproc_ =
  perform
    c <-- linchan;
    skip_symbol "<-";
    p <-- proc;
    return (c,p)

let topproc : (toplvl,'s) MParser.t =
  (perform
    procs <-- sep_by1 topproc_ (skip_symbol "and");
    skip_symbol ";;";
    return (TopProc procs))
  <?> "top level process"

let entrypoint =
  perform
    spaces;
    bindings <-- many (mtypedec <|> stypedec <|> topdef <|> topproc);
    eof;
    return bindings

(* TODO use In_channel.with_file. It should be safer *)
(* TODO figure how to read from stdin more sanely *)
let main (file: string) : toplvl list =
  if file = "-" 
  then match MParser.parse_string entrypoint (In_channel.input_all In_channel.stdin) () with
       | Success prog -> prog
       | Failed (msg, _) -> print_endline msg; Pervasives.exit 1
  else match MParser.parse_channel entrypoint (open_in file) () with
       | Success prog -> prog
       | Failed (msg, _) -> print_endline msg; Pervasives.exit 1
