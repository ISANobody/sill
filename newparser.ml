open Base
open Core.Std
open MParser
open MParser.Tokens

let keywords = ["fun"; "and"; "if"; "then"; "else"; "forall"; "exists"
               ;"let"; "in"; "send"; "recv"; "case"; "of"; "wait"
               ;"close"]

(* This is pretty ugly. The correct way to handle arbitrary paired comments is to treat
   eat them while consume spare white space. Of course, this isn't actually modularized
   so we need to rebind 'spaces' and some functions from MParser that use it. Ugh. *)

let rec comment_go_ : (unit,'s) MParser.t Lazy.t = lazy(
  (perform 
    skip_many_until any_char (attempt (skip_string "*)")
                             <|>
                             (perform
                               attempt (skip_string "(*");
                               Lazy.force comment_go_;
                               Lazy.force comment_go_)
                             );
    spaces)
  <?> "")
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
    (regexp (make_regexp "-?\\d+") >>= fun digits ->
     spaces           >>
     try_return int_of_string digits "Integer value out of range" s
     <?> "integer value") s

let float_tok s =
     (regexp (make_regexp "-?\\d+(\\.\\d*)?((e|E)?(\\+|-)?\\d+)?") >>= fun digits ->
     spaces         >>
     try_return Float.of_string digits "Not a valid float value" s
     <?> "float value") s

(* END OF COPIED JUNK *)

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

(* We allow one case where identifiers cannot be followed by spaces: branch selection.
   As a result some of these identifier parsers will have id_ versions that do not consume
   trailing spaces. *)

let id_lower_ : (string,'s) MParser.t =
  attempt (perform
    c <-- lowercase;
    cs <-- many_chars (alphanum <|> char '_' <|> char ''');
    let name = ((String.make 1 c) ^ cs)
    in if List.mem keywords name
       then zero
       else return name)
  <?> "lowercase identifier"

let id_lower = id_lower_ >>= fun s -> spaces >> return s

let id_upper : (string,'s) MParser.t =
  (perform
    c <-- uppercase;
    cs <-- many_chars (alphanum <|> char '_' <|> char ''');
    _ <-- spaces;
    return ((String.make 1 c) ^ cs))
  <?> "uppercase identifier"

let patvar = id_lower <|> symbol "_" <?> "pattern variable"

let id_lin_ =
  (perform
    skip_char ''';
    x <-- id_lower_;
    return ("'"^x))

let id_lin = id_lin_ >>= fun s -> spaces >> return s

let id_aff_ =
  (perform
    skip_char '@';
    x <-- id_lower_;
    return ("@"^x))

let id_aff = id_aff_ >>= fun s -> spaces >> return s

let id_shr_ =
  (perform
    skip_char '!';
    x <-- id_lower_;
    return ("!"^x))

let id_shr = id_shr_ >>= fun s -> spaces >> return s

let linchan = id_lin <?> "linear channel"
let affchan = id_aff <?> "affine channel"
let shrchan = id_shr <?> "unrestricted channel"
let subchan = id_lin <|> id_aff <?> "substructural channel"
let anychan_ = id_lin_ <|> id_aff_ <|> id_shr_ <?> "channel"
let anychan = id_lin <|> id_aff <|> id_shr <?> "channel"
let sesvar  = id_lin <|> id_aff <|> id_shr <?> "session type variable"
let datavar = id_lower <?> "data-level type variable"

let rec tyapp_ = lazy (
  perform
    name <-- id_upper;
    m    <-- many (  id_upper 
                 <|> attempt (Lazy.force mtype_atom_)
                 <|> attempt (Lazy.force stype_atom_)
                 <?> "data-level or session type");
    return (name^" "^intersperse " " m)
)
and mtype_atom_ = lazy(
  datavar
  <|>
  id_upper
  <|>
  (perform
    skip_symbol "()";
    return "()")
  <|>
  (perform
    skip_symbol "[";
    t <-- Lazy.force mtype_;
    skip_symbol "]";
    return ("["^t^"]"))
  <|>
  (perform
     skip_symbol "{";
     (skip_symbol "}" >> return "{ }")
     <|>
     (perform
       t <-- Lazy.force stype_;
       (skip_symbol "}" >> return ("{ "^t^" }"))
       <|>
       (perform
         skip_symbol "<-";
         ts <-- sep_by1_lazy (skip_symbol ";") stype_;
         skip_symbol "}";
         return ("{ "^t^" <- "^intersperse ":" ts^" }"))))
  <|>
  (perform
    skip_symbol "(";
    t1 <-- Lazy.force mtype_;
    (perform
       skip_symbol ",";
       t2 <-- Lazy.force mtype_;
       skip_symbol ")";
       return ("("^t1^", "^t2^")"))
    <|>
     (skip_symbol ")" >> return ("("^t1^")")))
  <?> "data-level type"
)
and mtype_basic_ = lazy(
   Lazy.force tyapp_
   <|>
   Lazy.force mtype_atom_
  <?> "data-level type"
)
and mtype_ = lazy(
  (perform
     t1 <-- Lazy.force mtype_basic_;
     arr <-- try_skip (skip_symbol "->");
     if arr
     then perform
            t2 <-- Lazy.force mtype_;
            return ("("^t1^") -> "^t2)
     else return t1)
  <?> "data-level type"
)
and stype_ = lazy(
  (perform
     attempt (skip_char '!' >> not_followed_by lowercase "" >> spaces);
     t <-- Lazy.force stype_;
     return ("!"^t))
  <|>
  (perform
     attempt (skip_char '@' >> not_followed_by lowercase "" >> spaces);
     t <-- Lazy.force stype_;
     return ("@"^t))
  <|>
  (perform
     attempt (skip_char ''' >> not_followed_by lowercase "" >> spaces);
     t <-- Lazy.force stype_;
     return ("'"^t))
  <|>
  attempt (perform
     m <-- Lazy.force mtype_;
     (perform
        skip_symbol "/\\";
        s <-- Lazy.force stype_;
        return (m^" /\\ "^s))
     <|>
     (perform
        skip_symbol "=>";
        s <-- Lazy.force stype_;
        return (m^" => "^s)))
  <|>
  (perform
    skip_symbol "forall";
    q <-- sesvar;
    skip_symbol ".";
    s <-- Lazy.force stype_;
    return ("forall "^q^" . "^s))
  <|>
  (perform
    skip_symbol "exists";
    q <-- sesvar;
    skip_symbol ".";
    s <-- Lazy.force stype_;
    return ("exists "^q^" . "^s))
  <|>
  Lazy.force stype_times_
  <?> "session type"
)
and stype_times_ = lazy(
  (perform
    s1 <-- Lazy.force stype_basic_;
    (perform 
      skip_symbol "*";
      s2 <-- Lazy.force stype_;
      return (s1^" * "^s2))
    <|>
    (perform 
      skip_symbol "-o";
      s2 <-- Lazy.force stype_;
      return (s1^" -o "^s2))
    <|>
    (return s1))
  <?> "session type"
)
and stype_basic_ = lazy(
  Lazy.force tyapp_
  <|>
  Lazy.force stype_atom_
  <?> "session type"
)
and stype_atom_ = lazy(
  sesvar
  <|>
  id_upper
  <|>
  (perform
     skip_symbol "1";
     return "1")
  <|>
  (perform
    skip_symbol "+{";
    ts <-- sep_by (perform
                     label <-- id_lower;
                     skip_symbol ":"; 
                     t <-- Lazy.force stype_;
                     return (label,t)) 
                  (skip_symbol ";");
    skip_symbol "}";
    return ("+{ "^intercal (fun (l,t) -> l^":"^t) "; " ts ^" }"))
  <|>
  (perform
    skip_symbol "&{";
    ts <-- sep_by (perform
                     label <-- id_lower;
                     skip_symbol ":"; 
                     t <-- Lazy.force stype_;
                     return (label,t)) 
                  (skip_symbol ";");
    skip_symbol "}";
    return ("&{ "^intercal (fun (l,t) -> l^":"^t) "; " ts ^" }"))
  <|>
  parens_lazy stype_
  <?> "session type"
)

let mtype = Lazy.force mtype_
let mtype_atom = Lazy.force mtype_atom_
let stype = Lazy.force stype_
let tyapp = Lazy.force tyapp_

let constructor =
  perform
    name <-- id_upper;
    args <-- many mtype_atom;
    return (name^" "^intersperse " " args)
  
let mtypedec =
  perform
    skip_symbol "type";
    id <-- id_upper;
    qs <-- many (sesvar <|> datavar);
    skip_symbol "=";
    t <-- sep_by constructor (skip_symbol "|");
    skip_symbol ";;";
    return (id^" "^intersperse " " qs
           ^" = "^intersperse "\n| " t)

let stypedec =
  perform
    (skip_symbol "ltype" <|> skip_symbol "atype" <|> skip_symbol "utype");
    id <-- id_upper;
    qs <-- many (sesvar <|> datavar);
    skip_symbol "=";
    t <-- stype;
    skip_symbol ";;";
    return (id^" "^intersperse " " qs^" = "^t)

let data_pattern =
  (perform
    skip_symbol "|";
    (perform
      name <-- id_upper;
      pats <-- many patvar;
      skip_symbol "->";
      return ("| "^name^" "^intersperse " " pats^" -> "))
    <|>
    (perform
      skip_symbol "[]";
      skip_symbol "->";
      return ("| [] -> "))
    <|>
    (perform
      skip_symbol "(";
      x1 <-- patvar;
      skip_symbol ",";
      x2 <-- patvar;
      skip_symbol ")";
      skip_symbol "->";
      return ("| ("^x1^","^x2^") -> "))
    <|>
    (perform
      x1 <-- patvar;
      skip_symbol "::";
      x2 <-- patvar;
      skip_symbol "->";
      return ("| "^x1^"::"^x2^" -> ")))
  <?> "pattern match"

let rec exp_ = lazy(
  (perform 
    e1 <-- Lazy.force exp_and_;
    (perform
      skip_symbol "||";
      e2 <-- Lazy.force exp_;
      return (e1^" || "^e2))
    <|>
    (return e1))
  <?> "expression"
)
and exp_and_ = lazy(
  (perform
    e1 <-- Lazy.force exp_eq_;
    (perform
      skip_symbol "&&";
      e2 <-- Lazy.force exp_and_;
      return (e1^" && "^e2))
    <|>
    (return e1))
)
and exp_eq_ = lazy(
  (perform
    e1 <-- Lazy.force exp_compare_;
    (perform
      skip_symbol "=";
      e2 <-- Lazy.force exp_eq_;
      return (e1^" = "^e2))
    <|>
    (return e1))
)
and exp_compare_ = lazy(
  (perform
    e1 <-- Lazy.force exp_cons_;
    (perform
      skip_symbol "<=";
      e2 <-- Lazy.force exp_eq_;
      return (e1^" <= "^e2))
    <|>
    (perform
      skip_symbol ">=";
      e2 <-- Lazy.force exp_eq_;
      return (e1^" => "^e2))
    <|>
    (perform
      skip_symbol "<";
      e2 <-- Lazy.force exp_eq_;
      return (e1^" < "^e2))
    <|>
    (perform
      skip_symbol ">";
      e2 <-- Lazy.force exp_eq_;
      return (e1^" > "^e2))
    <|>
    (return e1))
)
and exp_cons_ = lazy(
  (perform
    e1 <-- Lazy.force exp_add_;
    (perform
      skip_symbol "::";
      e2 <-- Lazy.force exp_;
      return (e1^" :: "^e2))
    <|>
    (return e1))
)
and exp_add_ = lazy(
  (perform
    e1 <-- Lazy.force exp_times_;
    (perform
      skip_symbol "+.";
      e2 <-- Lazy.force exp_;
      return (e1^" +. "^e2))
    <|>
    (perform
      skip_symbol "-.";
      e2 <-- Lazy.force exp_;
      return (e1^" -. "^e2))
    <|>
    (perform
      skip_symbol "+";
      e2 <-- Lazy.force exp_;
      return (e1^" + "^e2))
    <|>
    (perform
      (attempt (char '-' >> not_followed_by (char '<') "" >> spaces));
      e2 <-- Lazy.force exp_;
      return (e1^" - "^e2))
    <|>
    (perform
      skip_symbol "^";
      e2 <-- Lazy.force exp_;
      return (e1^" ^ "^e2))
    <|>
    (return e1))
)
and exp_times_ = lazy(
  (perform
    e1 <-- Lazy.force exp_exp_;
    (perform
      skip_symbol "*.";
      e2 <-- Lazy.force exp_times_;
      return (e1^" *. "^e2))
    <|>
    (perform
      skip_symbol "/.";
      e2 <-- Lazy.force exp_times_;
      return (e1^" /. "^e2))
    <|>
    (perform
      skip_symbol "*";
      e2 <-- Lazy.force exp_times_;
      return (e1^" * "^e2))
    <|>
    (perform
      skip_symbol "/";
      e2 <-- Lazy.force exp_times_;
      return (e1^" / "^e2))
    <|>
    (return e1))
  <?> "expression"
)
and exp_exp_ = lazy(
  (perform
    e1 <-- Lazy.force exp_app_;
    (perform
      skip_symbol "**";
      e2 <-- Lazy.force exp_exp_;
      return (e1^" ** "^e2))
    <|>
    (return e1))
  <?> "expression"
)
and exp_app_ = lazy(
  (perform
    es <-- many1 (Lazy.force exp_basic_);
    return (intersperse " " es))
  <?> "expression"
)
and exp_basic_ = lazy(
  (perform
    skip_symbol "fun";
    vars <-- many1 patvar;
    skip_symbol "->";
    e <-- Lazy.force exp_;
    return ("fun "^intersperse " " vars^" -> "^e))
  <|>
  (perform
    skip_symbol "let";
    name <-- id_lower;
    vars <-- many patvar;
    skip_symbol ":";
    t <-- mtype;
    skip_symbol "=";
    e1 <-- Lazy.force exp_;
    skip_symbol "in";
    e2 <-- Lazy.force exp_;
    return (name^" "^intersperse " " vars^" : "^t^" = "^e1^"\n in "^e2))
  <|>
  (perform
    skip_symbol "if";
    ec <-- Lazy.force exp_;
    skip_symbol "then";
    et <-- Lazy.force exp_;
    skip_symbol "else";
    ef <-- Lazy.force exp_;
    return ("if "^ec^" then "^et^" else "^ef))
  <|>
  (perform
    skip_symbol "case";
    e <-- Lazy.force exp_;
    skip_symbol "of";
    es <-- many1 (perform
                   pat <-- data_pattern;
                   ep <-- Lazy.force exp_;
                   return (pat^ep));
    return ("case "^e^" of "^intersperse "\n" es))
  <|>
  (perform
    c <-- anychan;
    skip_symbol "<-";
    skip_symbol "{";
    p <-- Lazy.force proc_;
    skip_symbol "}";
    (perform
      skip_symbol "-<";
      cs <-- many anychan;
      return (c^" <-{ "^p^" }-< "^intersperse " " cs))
    <|>
    (return (c^" <-{ "^p^" }")))
  <|>
  Lazy.force exp_atom_
  <?> "expression"
)
and exp_atom_ = lazy(
  (perform
    x <-- id_lower_;
    (perform
      skip_char '<';
      ts <-- sep_by (attempt stype <|> attempt mtype) (symbol ",");
      skip_char '>';
      spaces;
      return (x^"<"^intersperse "," ts^">"))
    <|>
    (spaces >> return x))
  <|>
  id_upper
  <|>
  attempt (float_tok |>> Float.to_string)
  <|>
  attempt (integer |>> string_of_int)
  <|>
  attempt (skip_symbol "()" >> return "()")
  <|>
  attempt string_literal
  <|>
  (perform
    (attempt (char '<' >> not_followed_by (  char '=' 
                                         <|> char '''
                                         <|> char '@'
                                         <|> char '!') "" >> spaces));
    e <-- Lazy.force exp_;
    skip_symbol ":";
    t <-- mtype;
    skip_symbol ">";
    return ("< "^e^" : "^t^" >"))
  <|>
  (perform
     skip_symbol "[";
     es <-- sep_by_lazy (skip_symbol ";") exp_;
     skip_symbol "]";
     return ("["^intersperse "; " es^"]"))
  <|>
  (perform
     skip_symbol "(";
     e1 <-- Lazy.force exp_;
     (perform
       skip_symbol ",";
       e2 <-- Lazy.force exp_;
       skip_symbol ")";
       return ("("^e1^", "^e2^")"))
     <|>
     (skip_symbol ")" >> return ("("^e1^")")))
  <?> "expression"
)
and proc_inst_ = lazy(
  (perform
    skip_symbol "if";
    ec <-- Lazy.force exp_;
    skip_symbol "then";
    pt <-- Lazy.force proc_;
    skip_symbol "else";
    pf <-- Lazy.force proc_;
    return ("if "^ec^" then "^pt^" else "^pf))
  <|>
  (perform
    skip_symbol "case";
    (perform
      c <-- subchan;
      skip_symbol "of";
      cases <-- many (perform 
                       skip_symbol "|";
                       l <-- id_lower;
                       skip_symbol "->";
                       p <-- Lazy.force proc_;
                       return ("| "^l^" -> "^p));
      return ("case "^c^" of\n"^intersperse "\n" cases))
    <|>
    (perform
      e <-- Lazy.force exp_;
      skip_symbol "of";
      cases <-- many1 (perform
                         pat <-- data_pattern;
                         p <-- Lazy.force proc_;
                         return (pat^p));
    return ("case "^e^" of\n"^intersperse "\n" cases)))
  <|>
  attempt (Lazy.force exp_)
  <|>
  (perform
    skip_symbol "<";
    x <-- sesvar;
    skip_symbol ">";
    skip_symbol "<-";
    skip_symbol "recv";
    c <-- subchan;
    return ("<"^x^"> <- recv "^c))
  <|>
  (perform 
    skip_symbol "close";
    c <-- subchan;
    return ("close "^c))
  <|>
  (perform 
    skip_symbol "wait";
    c <-- subchan;
    return ("wait "^c))
  <|>
  (perform
    skip_symbol "let";
    name <-- id_lower;
    pats <-- many patvar;
    skip_symbol ":";
    t <-- mtype;
    skip_symbol "=";
    e <-- Lazy.force exp_;
    return ("let "^name^" "^intersperse " " pats^" : "^t^" = "^e))
  <|>
  (perform 
    skip_symbol "send";
    c <-- subchan;
    (perform
      e <-- attempt (Lazy.force exp_);
      return ("send "^c^" "^e))
    <|>
    (perform
      c' <-- subchan;
      return ("send "^c^" "^c'))
    <|>
    (perform
      skip_symbol "(";
      c2 <-- anychan;
      skip_symbol "<-";
      p <-- Lazy.force proc_;
      skip_symbol ")";
      return ("send "^c^" ("^c2^" <- "^p^")"))
    <|>
    (perform
      skip_symbol "<";
      t <-- stype;
      skip_symbol ">";
      return ("send "^c^" <"^t^">"))
  )
  <|>
  (perform
    x <-- id_lower;
    skip_symbol "<-";
    skip_symbol "recv";
    c <-- subchan;
    return (x^" <- recv "^c))
  <|>
  (perform
    skip_symbol "_";
    skip_symbol "<-";
    (perform
      skip_symbol "recv";
      c <-- subchan;
      return ("_ <- recv "^c))
    <|>
    (perform
      e <-- Lazy.force exp_;
      (perform
        skip_symbol "-<";
        cs <-- many anychan;
        return ("_ <- "^e^" -< "^intersperse " " cs))
      <|>
      (return ("_ <- "^e))))
  <|>
  (perform
    c1 <-- anychan_;
    (perform
      skip_char '.';
      l <-- id_lower;
      return (c1^"."^l))
    <|>
    (perform
      spaces;
      skip_symbol "<-";
      (skip_symbol "recv" >>
        (perform
          c2 <-- anychan;
          return (c1^" <- recv "^c2)))
      <|>
      (perform
        c2 <-- subchan;
        return (c1^" <- "^c2))
      <|>
      (perform
        e <-- Lazy.force exp_;
        (perform
          skip_symbol "-<";
          cs <-- many anychan;
          return (c1^" <- "^e^" -< "^intersperse " "cs))
        <|>
        (return (c1^" <- "^e)))
      <|>
      (perform
        skip_symbol "send";
        c2 <-- anychan;
        return (c1^" <- send "^c2)))
  )
  <|>
  parens_lazy proc_
  <?> "process statement"
)
and proc_ = lazy(
  (perform
    pis <-- sep_by1_lazy (attempt (char ';' >> not_followed_by (char ';') "" >> spaces)) proc_inst_;
    return (intersperse ";\n" pis))
  <?> "process"
)

let exp = Lazy.force exp_
let proc = Lazy.force proc_

let topsig =
  perform
    name <-- id_lower;
    skip_symbol ":";
    (perform
      skip_symbol "forall";
      skip_symbol "<";
      qs <-- sep_by (datavar <|> sesvar) (skip_symbol ",");
      skip_symbol ">";
      skip_symbol ".";
      t <-- mtype;
      return (name^" : forall "^intersperse " " qs^" . "^t))
    <|>
    (perform
      t <-- mtype;
      return (name^" : "^t))

let topdef_ = 
  perform
    t <-- topsig;
    skip_symbol ";;";
    (perform
      name <-- id_lower;
      pats <-- many patvar;
      skip_symbol "=";
      e <-- exp;
      return (t^"\n"^name^" "^intersperse " " pats^" = "^e))
    <|>
    (perform
       c <-- (anychan <|> symbol "_");
       skip_symbol "<-";
       name <-- id_lower;
       pats <-- many patvar;
       (perform
         skip_symbol "=";
         p <-- proc;
         return (t^"\n"^c^" <- "^name^" = "^p))
       <|>
       (perform
          skip_symbol "-<";
          cs <-- many anychan;
          skip_symbol "=";
          p <-- proc;
          return (t^"\n"^c^" <- "^name^" "^intersperse " " pats^" -< "
                 ^intersperse " " cs^" = "^p)))

let topdef = 
  perform
    defs <-- sep_by topdef_ (skip_symbol "and");
    skip_symbol ";;";
    return (intersperse "\nand\n" defs)

let topproc_ =
  perform
    c <-- linchan;
    skip_symbol "<-";
    p <-- proc;
    return (c^" <- "^p)

let topproc =
  perform
    procs <-- sep_by topproc_ (skip_symbol "and");
    skip_symbol ";;";
    return (intersperse "\nand\n" procs)

let entrypoint =
  perform
    skip_many comment;
    bindings <-- many (mtypedec <|> stypedec <|> topdef <|> topproc);
    return (print_endline (intersperse "\n" bindings));
    eof

let main (file: string) : unit =
  match MParser.parse_channel entrypoint (open_in file) () with
    | Success _ -> ()
    | Failed (msg, _) -> print_endline msg; Pervasives.exit 1
