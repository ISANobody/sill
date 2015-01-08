{

open Base
open Parse

exception EndInput

exception OpenComm of srcloc
exception CloseComm of srcloc
exception SuperCloseComm of srcloc

let cinc n = curloc := {!curloc with cnum = !curloc.cnum + n}
let linc n = curloc := {cnum = 1; lnum = !curloc.lnum + n}

let mkloc c = let l = !curloc
              in cinc c;
                 l

}

(* You can assign names to commonly-used regular expressions in this part
   of the code, to save the trouble of re-typing them each time they are used *)

let numeric = ['0' - '9']
let lowercase = ['a' - 'z']
let uppercase = ['A' - 'Z']
let letter =['a' - 'z' 'A' - 'Z' '_']

let funName = lowercase letter*
let id_char = numeric | letter | "'"
let open_comment = "(*" 
let close_comment = "*)"
let super_close_comment = "**)"

rule token = parse
  | [' ' '\t'] { cinc 1; token lexbuf }  (* skip over whitespace *)
  | ['\n' '\r'] { linc 1; token lexbuf }  (* skip over whitespace *)
  | eof             { EOF } 

(* your rules go here *)
  | ":"         { cinc 1; COLON }
  | ";;" 	{ cinc 2; DBLSEMI  }
  | "+" 	{ cinc 1; PLUS  }
  | "-" 	{ cinc 1; MINUS  }
  | "*" 	{ cinc 1; TIMES  }
  | "/" 	{ cinc 1; DIV  }
  | "+." 	{ cinc 2; DPLUS  }
  | "-." 	{ cinc 2; DMINUS  }
  | "*." 	{ cinc 2; DTIMES  }
  | "/." 	{ cinc 2; DDIV  }
  | "^" 	{ cinc 1; CARAT  }
  | "**" 	{ cinc 2; EXP  }
  | "<" 	{ cinc 1; LT  }
  | ">" 	{ cinc 1; GT  }
  | "<=" 	{ cinc 2; LEQ  }
  | ">=" 	{ cinc 2; GEQ  }
  | "=" 	{ EQUALS (mkloc 1)  }
  | "&&" 	{ cinc 2; AND  }
  | "and"       { cinc 2; MUTAND }
  | "||" 	{ OR (mkloc 2) }
  | "|" 	{ cinc 1; PIPE  }
  | "->" 	{ cinc 2; ARROW  }
  | "<-" 	{ cinc 2; LARROW  }
  | "-<"        { cinc 2; TAIL }
  | "::" 	{ cinc 2; DCOLON  }
  | "let" 	{ LET (mkloc 3) }
  | "~" 	{ NEG (mkloc 1) }
  | ";" 	{ cinc 1; SEMI  }
  | "in" 	{ cinc 2; IN  }
  | "if" 	{ IF (mkloc 2) }
  | "then" 	{ cinc 4; THEN  }
  | "else" 	{ cinc 4; ELSE  }
  | "fun" 	{ FUN (mkloc 3) }
  | "[" 	{ LBRAC (mkloc 1) }
  | "]" 	{ RBRAC (mkloc 1) }
  | "(" 	{ cinc 1; LPAREN  }
  | ")" 	{ cinc 1; RPAREN  }
  | "{" 	{ cinc 1; LBRACE  }
  | "}" 	{ cinc 1; RBRACE  }
  | "," 	{ cinc 1; COMMA  }
  | "_"		{ UNDERSCORE (mkloc 1) }
  | "abort"     { ABORT (mkloc 5) }
  | "type"      { cinc 4; TYPE }
  | "ltype"     { cinc 5; STYPE Linear }
  | "atype"     { cinc 5; STYPE Affine }
  | "utype"     { cinc 5; STYPE Intuist }
  | "proc"      { cinc 4; PROC }
  | "case"      { CASE (mkloc 4) }
  | "of"        { cinc 2; OF }
  | "recv"      { INPUT (mkloc 4) }
  | "send"      { OUTPUT (mkloc 4) }
  | "close"     { CLOSE (mkloc 5) }
  | "wait"      { WAIT (mkloc 4) }
  | "service"   { SERVICE (mkloc 7) }
  | "register"  { REGISTER (mkloc 8) }
  | "=>"        { cinc 2; SHOE }
  | "/\\"       { cinc 2; WEDGE }
  | "-o"        { cinc 2; LOLI }
  | "ALL"       { cinc 3; ALL }
  | "."         { cinc 1; DOT }
  | "+{"        { cinc 2; OPLUS }
  | "&{"        { cinc 2; AMPR }
  | "forall"    { cinc 6; FORALL }
  | "exists"    { cinc 6; EXISTS }

  | numeric+ as s { INT (mkloc (String.length s),(int_of_string s)) }
  | (numeric+'.'(numeric*)) as s       { FLOAT (mkloc (String.length s),(float_of_string s)) }

  | "()"	{ UNIT (mkloc 2) }

  | (lowercase (id_char*)) as s		{ FUNNAME (mkloc (String.length s),s) }
  | (uppercase (id_char*)) as s		{ TYNAME (mkloc (String.length s), s) }
  | '\'' (lowercase (id_char*) as s)    { LINCHAN (mkloc (1+String.length s),s) }
  | '!' (lowercase (id_char*) as s)   { SHRCHAN (mkloc (1+String.length s),s) }
  | '@' (lowercase (id_char*) as s)   { AFFCHAN (mkloc (1+String.length s),s) }
  | '#' (lowercase (id_char*) as s)   { SVNAME (mkloc (1+String.length s),s) }
  | ((lowercase (id_char*)) as s) '<' { POLY (mkloc (1+String.length s),s) }

  | "!"         { cinc 1; BANG }
  | "'"         { cinc 1; PRIME }
  | "@"         { cinc 1; AT }

  | ("//"([^'\n' '\r']*)) as s	   { cinc (String.length s); token lexbuf }
  | open_comment	   { comment [mkloc 2] lexbuf }
  | close_comment	   { raise (CloseComm !curloc) }
  | super_close_comment	   { raise (SuperCloseComm !curloc) }

  | "\""	{ cinc 1; string "" lexbuf }

and comment open_dimens = parse 
   open_comment        { comment (mkloc 2::open_dimens) lexbuf } 
 | close_comment       { cinc 2;
                         match open_dimens with [pos] -> token lexbuf 
                         | dim::dimens -> comment dimens lexbuf
			 | [] -> failwith "Closed comments too much? Probably Lex error" } 
 | super_close_comment { cinc 3; token lexbuf }
 | eof		       { raise (OpenComm (List.hd open_dimens)) }
 | ['\n' '\r']                { linc 1; comment open_dimens lexbuf }
 | _                   { cinc 1; comment open_dimens lexbuf }

and string start_string = parse
   "\""	   	{ STRING (mkloc 1,start_string) }
 | "\\\\"	{ cinc 2; string (start_string ^ "\\") lexbuf }
 | "\\'"	{ cinc 2; string (start_string ^ "'") lexbuf }
 | "\\\""	{ cinc 2; string (start_string ^ "\"") lexbuf }
 | "\\t"	{ cinc 2; string (start_string ^ "\t") lexbuf }
 | "\\n"	{ cinc 2; string (start_string ^ "\n") lexbuf }
 | "\\r"	{ cinc 2; string (start_string ^ "\r") lexbuf }
 | "\n"		{ linc 1; string (start_string ^ "\n") lexbuf }
 | _ as c	{ cinc 1; string (start_string ^ (String.make 1 c)) lexbuf }
