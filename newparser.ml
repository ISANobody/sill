open Base
open Core.Std
open MParser
open MParser.Tokens

let rec sep_by1_lazy sep (p : ('a,'s) MParser.t Lazy.t) : ('a list,'s) MParser.t =
  perform
    x <-- Lazy.force p;
    xs <-- many (sep >> Lazy.force p);
    return (x::xs)

let between_lazy left right (p : ('a,'s) MParser.t Lazy.t) : ('a,'s) MParser.t =
  perform
    skip_char left;
    _ <-- spaces;
    ret <-- Lazy.force p;
    skip_char right;
    _ <-- spaces;
    return ret

let parens_lazy p = between_lazy '(' ')' p

let id_lower : (string,'s) MParser.t =
  (perform
    c <-- lowercase;
    cs <-- many_chars (alphanum <|> char '_' <|> char ''');
    _ <-- spaces;
    return ((String.make 1 c) ^ cs))
  <?> "lowercase identifier"

let id_upper : (string,'s) MParser.t =
  (perform
    c <-- uppercase;
    cs <-- many_chars (alphanum <|> char '_' <|> char ''');
    _ <-- spaces;
    return ((String.make 1 c) ^ cs))
  <?> "uppercase identifier"

let id_lin =
  (perform
    skip_char ''';
    x <-- id_lower;
    return ("'"^x))

let id_aff =
  (perform
    skip_char '@';
    x <-- id_lower;
    return ("@"^x))

let id_shr =
  (perform
    skip_char '!';
    x <-- id_lower;
    return ("!"^x))

let linchan = id_lin <?> "linear channel"
let affchan = id_aff <?> "affine channel"
let shrchan = id_shr <?> "unrestricted channel"
let subchan = id_lin <|> id_aff <?> "substructural channel"
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
     t <-- Lazy.force stype_;
     (skip_symbol "}"
     <|>
     (perform
        skip_symbol "<-";
        _ <-- sep_by1_lazy (skip_symbol ";") stype_;
        skip_symbol "}")
     );
     return ("{"^t^"}"))
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
     skip_symbol "!";
     t <-- Lazy.force stype_;
     return ("!"^t))
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

let exp = integer |>> string_of_int
and proc = 
  perform 
    skip_symbol "close";
    c <-- anychan;
    return ("close "^c)

let topsig =
  perform
    name <-- id_lower;
    skip_symbol ":";
    (perform
      skip_symbol "forall";
      qs <-- many (datavar <|> sesvar);
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
      pats <-- many (id_lower <|> symbol "_");
      skip_symbol "=";
      e <-- exp;
      return (t^"\n"^name^" "^intersperse " " pats^" = "^e))
    <|>
    (perform
       c <-- anychan;
       skip_symbol "<-";
       name <-- id_lower;
       pats <-- many (id_lower <|> symbol "_");
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
    bindings <-- many (mtypedec <|> stypedec <|> topdef <|> topproc);
    return (print_endline (intersperse "\n" bindings));
    eof

let main (file: string) : unit =
  match MParser.parse_channel entrypoint (open_in file) () with
    | Success _ -> ()
    | Failed (msg, _) -> print_endline msg; Pervasives.exit 1
