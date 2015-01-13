open Base
open Core.Std
open MParser
open MParser.Tokens

let rec list_ne_lazy (sep : string) (p : ('a,'s) MParser.t Lazy.t) : ('a list,'s) MParser.t =
  let sep' = if sep = " " then zero else skip_symbol sep in
  perform
    a <-- Lazy.force p;
    (perform
       o <-- option (sep' >> list_ne_lazy sep p);
       match o with
       | Some tail -> return (a::tail)
       | None      -> return [a])

let rec list_ne (sep : string) (p : ('a,'s) MParser.t) : ('a list,'s) MParser.t =
  let sep' = if sep = " " then zero else skip_symbol sep in
  perform
    a <-- p;
    (perform
       o <-- option (sep' >> list_ne sep p);
       match o with
       | Some tail -> return (a::tail)
       | None      -> return [a])

let id_lower : (string,'s) MParser.t =
  (perform
    c <-- lowercase;
    cs <-- many_chars (alphanum <|> char '_');
    _ <-- spaces;
    return ((String.make 1 c) ^ cs))
  <?> "lowercase identifier"

let id_upper : (string,'s) MParser.t =
  (perform
    c <-- uppercase;
    cs <-- many_chars (alphanum <|> char '_');
    _ <-- spaces;
    return ((String.make 1 c) ^ cs))
  <?> "uppercase identifier"

let id_lin =
  perform
    skip_char ''';
    x <-- id_lower;
    return ("'"^x)

let id_aff =
  perform
    skip_char '@';
    x <-- id_lower;
    return ("@"^x)

let id_shr =
  perform
    skip_char '!';
    x <-- id_lower;
    return ("!"^x)

let subchan = id_lin <|> id_aff <?> "substructural channel"
let anychan = id_lin <|> id_aff <|> id_shr <?> "channel"
let sesvar  = id_lin <|> id_aff <|> id_shr <?> "session type variable"
let datavar = id_lower <?> "data-level type variable"

let rec tyapp_ = lazy (
  perform
    name <-- id_upper;
    m    <-- many (attempt (Lazy.force mtype_ <|> Lazy.force stype_));
    return (name^" "^intercal (fun x -> x) " " m)
)
and mtype_ = lazy(
  datavar
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
        _ <-- list_ne_lazy ";" stype_;
        skip_symbol "}")
     );
     return ("{"^t^"}"))
  <|>
  (perform
    skip_symbol "(";
    t <-- Lazy.force mtype_;
    skip_symbol ")";
    return ("("^t^")"))
  <?> "data-level type"
)
and stype_ = lazy(
  attempt sesvar
  <|>
  Lazy.force tyapp_
  <|>
  (perform
     skip_symbol "1";
     return "1")
  <|>
  (perform
     skip_symbol "!";
     t <-- Lazy.force stype_;
     return ("!"^t))
  <|>
  (perform
    skip_symbol "(";
    t <-- Lazy.force stype_;
    skip_symbol ")";
    return ("("^t^")"))
  <?> "session type"
)

let mtype = Lazy.force mtype_
let stype = Lazy.force stype_
let tyapp = Lazy.force tyapp_

let constructor =
  perform
    name <-- id_upper;
    args <-- many mtype;
    return (name^" "^intercal (fun x -> x) " " args)
  
let mtypedec : (unit,'s) MParser.t =
  perform
    skip_symbol "type";
    id <-- id_upper;
    qs <-- many (sesvar <|> datavar);
    skip_symbol "=";
    t <-- sep_by constructor (skip_symbol "|");
    skip_symbol ";;";
    return (print_endline (id^" "^intercal (fun x -> x) " " qs
                          ^" = "^intercal (fun x -> x) "\n| " t))

let stypedec : (unit,'s) MParser.t =
  perform
    (skip_symbol "ltype" <|> skip_symbol "atype" <|> skip_symbol "utype");
    id <-- id_upper;
    qs <-- many (sesvar <|> datavar);
    skip_symbol "=";
    t <-- stype;
    skip_symbol ";;";
    return (print_endline (id^" "^intercal (fun x -> x) " " qs^" = "^t))

let entrypoint = many (mtypedec <|> stypedec) >> eof

let main (file: string) : unit =
  match MParser.parse_channel entrypoint (open_in file) () with
    | Success _ -> ()
    | Failed (msg, _) -> print_endline msg; Pervasives.exit 1
