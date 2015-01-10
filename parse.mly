%{

open Base
open Vars
open Types
open Puretypes
open Fullsyntax
open Connection
open Ambig

(* exceptions for type declarations *)
(* provide some context when we can *)
exception ReusedConstructor of string
exception ReusedTypeName of string
exception UnboundConstructor of string
exception UnboundTypeVar of (string * string)
exception UnboundTypeName of string
exception EmptyCase
exception DifferentCaseTypes
exception NonLinearPattern


(* TODO move this to desugar.ml? *)
let namecheck tysig (body:fvar) : unit =
  if not (fvar_eq (fst tysig) body) 
  then errr (fst (fst tysig)) ("Signature for wrong function. Wanted "
                              ^snd body^" got "^snd (fst tysig))

let chan2tyvar (c:cvar) : tyvar =
  match c with
  | (_,Lin x) -> (Linear,x)
  | (_,Aff x) -> (Affine,x)
  | (_,Shr x) -> (Intuist,x)

let chan2svar (c:cvar) : stype =
  match c with
  | (_,Lin x) -> SVar (fst c,(Linear,x))
  | (_,Aff x) -> SVar (fst c,(Affine,x))
  | (_,Shr x) -> SVar (fst c,(Intuist,x))

let abrace2mtype ((c1,c2):(cvar * cvar)) : mtype =
  MonT (Some (chan2svar c1),[chan2svar c2])

let abrace2proc ((c1,c2):(cvar * cvar)) : proc =
  Fwd (fst c1,c1,c2)

%}

/* Define the tokens of the language: */
%token <Base.srcloc*int> INT
%token <Base.srcloc*float> FLOAT
%token <Base.srcloc*string> LINCHAN SHRCHAN AFFCHAN FUNNAME STRING TYNAME POLY
%token <(int*int)> OPCOM CLCOM SCLCOM
%token <Base.srcloc> RBRAC UNDERSCORE CLOSE AWAIT WAIT CASE INPUT OUTPUT FUN 
                     EQUALS LET OR IF NEG ABORT UNIT LBRAC SERVICE REGISTER
                     SEMI LPAREN LOLI TIMES DOT COLON LBRACE OPLUS AMPR
                     SHOE WEDGE AT BANG PRIME LARROW FORALL COMMA
%token DBLSEMI PLUS MINUS DIV DPLUS DMINUS DTIMES DDIV CARAT EXP LT GEQ LEQ GT
       AND PIPE ARROW DCOLON IN THEN ELSE TYPE LIST
       RPAREN
       ERROR EOF
       OF POLL
       RBRACE
       PROC TAIL
       BANG DIAMOND ASSERT MUTAND EXISTS

%token<Base.modality> STYPE 

%right WEDGE SHOE
%left  LOLI 

/* Define the "goal" nonterminal of the grammar: */
%start main
%type <Fullsyntax.toplvl list> main
%type <mtype> monotype_atom
%type <stype> sessiontype
%type <mtype list SM.t> constructors
%type <stype LM.t> choices

/* Intermediate changes */
%type <cvar> linchan shrchan
%type <cvar list> chanlist
%type <exp> expression pure_or_exp or_exp and_exp app_exp expo_exp mult_exp add_exp cons_exp rel_exp
%type <proc> process
%type <ambig> ambig ambig_notimesarr ambig_noarr

%%

main:
  | /* empty */ { [] }
  | typedecl main { $1 :: $2 }
  | code main { $1 :: $2 }

ambig:
  | ambig_noarr { $1 }
  | ambig_noarr ARROW ambig { Arrow ($1,$3) }

ambig_noarr:
  | ambig_notimesarr  { $1 }
  | ambig_notimesarr TIMES ambig { Times ($1,$3) }

ambig_notimesarr:
  | TYNAME                            { Seqq [Tyname (fst $1,snd $1)] }
  | FUNNAME                           { Seqq [Funname (fst $1,snd $1)] }
  | UNIT                              { Seqq [Unit $1] }
  | INT                               { Seqq [Int (fst $1,snd $1)] }
  | LPAREN ambig RPAREN               { Seqq [Paren $2] }
  | LBRAC ambig RBRAC                 { Seqq [List $2] }
  | LPAREN ambig COMMA ambig RPAREN   { Seqq [Pair ($2,$4)] }
  | atomic_expression                 { Seqq [EAtom $1] }
  | monotype_atom                     { Seqq [MAtom $1] }
  | ambig_notimesarr atomic_expression   { ambigsnoc $1 (EAtom $2) }
  | ambig_notimesarr monotype_atom       { ambigsnoc $1 (MAtom $2) }
  | ambig_notimesarr TYNAME              { ambigsnoc $1 (Tyname (fst $2,snd $2)) }
  | ambig_notimesarr FUNNAME             { ambigsnoc $1 (Funname (fst $2,snd $2)) }
  | ambig_notimesarr UNIT                { ambigsnoc $1 (Unit $2) }
  | ambig_notimesarr INT                 { ambigsnoc $1 (Int (fst $2,snd $2)) }
  | ambig_notimesarr LPAREN ambig RPAREN { ambigsnoc $1 (Paren $3) }
  | ambig_notimesarr LBRAC ambig RBRAC   { ambigsnoc $1 (List $3) }

ambig_brace:
  | LBRACE linchan LARROW linchan RBRACE { ($2,$4) }

typedecl:
  | TYPE TYNAME vars EQUALS constructors
    { MTypeDecl ($2,$3,$5) }
    /* { typeNames := SS.add !typeNames (snd $2);
      SM.iter $5 (fun ~key:c ~data:a -> 
        conTypeNames := SM.add !conTypeNames c (snd $2);
        conArities := SM.add !conArities c (List.length a);
        conTypes := SM.add !conTypes c 
                    (List.map vartoptr (SS.to_list $3)
                    ,List.map puretoptrM a))} */
  | STYPE TYNAME vars EQUALS sessiontype DBLSEMI 
    { STypeDecl ($1,$2,$3,$5) }
  | STYPE TYNAME vars EQUALS addtail DBLSEMI 
    { STypeDecl ($1,$2,$3,$5 Linear) }
  | STYPE TYNAME vars EQUALS ambig DBLSEMI 
    { STypeDecl ($1,$2,$3,ambigstype $5) }
  | SERVICE TYNAME EQUALS sessiontype DBLSEMI
    { ServDecl ($2,$4) }

vars:
  | /* empty */ { [] }
  | FUNNAME vars { $1::$2 }

constructors:
  | DBLSEMI { SM.empty }
  | ambig DBLSEMI { let (name,args) = ambigconst $1 in SM.singleton name args }
  | ambig PIPE constructors { let (name,args) = ambigconst $1 in SM.add $3 name args }

code:
  | topprocs DBLSEMI { TopProc $1 }
  | toplets DBLSEMI { TopLets $1 }

topprocs:
  | linchan LARROW process { [($1,$3)] }
  | linchan LARROW process MUTAND topprocs { ($1,$3)::$5 }

toplets: 
  | toplet { FM.singleton (fst $1) (snd $1) }
  | toplet MUTAND toplets { FM.add $3 (fst $1) (snd $1) }

eqpats:
 | EQUALS { [] }
 | patvar eqpats { $1 :: $2 }

arrowpats:
  | ARROW { [] }
  | patvar arrowpats { $1::$2 }

tailpats:
  | TAIL { [] }
  | patvar tailpats { $1::$2 }

colonpats:
  | COLON { [] }
  | patvar colonpats { $1::$2 }

netyvarlist: 
  | LINCHAN { [`S (Linear,snd $1)] }
  | AFFCHAN { [`S (Affine,snd $1)] }
  | SHRCHAN { [`S (Intuist,snd $1)] }
  | FUNNAME { [`M (snd $1)] }
  | LINCHAN COMMA netyvarlist { (`S (Linear,snd $1)) :: $3 }
  | AFFCHAN COMMA netyvarlist { (`S (Affine,snd $1)) :: $3 }
  | SHRCHAN COMMA netyvarlist { (`S (Intuist,snd $1)) :: $3 }
  | FUNNAME COMMA netyvarlist { (`M (snd $1)) :: $3 }
  | error COMMA netyvarlist { errr $2 "Expected type variable (x/'x/@x/!x) before ','." }
  | FUNNAME COMMA error { errr $2 "Expected type variable (x/'x/@x/!x) after ','." }
  | LINCHAN COMMA error { errr $2 "Expected type variable (x/'x/@x/!x) after ','." }
  | AFFCHAN COMMA error { errr $2 "Expected type variable (x/'x/@x/!x) after ','." }
  | SHRCHAN COMMA error { errr $2 "Expected type variable (x/'x/@x/!x) after ','." }

topsig:
  | FUNNAME COLON error    { errr $2 "Expected a data-level type after ':' here." }
  | FUNNAME COLON error DBLSEMI   { errr $2 "Expected a data-level type after ':' here." }
  | FUNNAME COLON ambig DBLSEMI    { ($1,`M (ambigmtype $3)) }
  | FUNNAME COLON ambig_brace DBLSEMI  { ($1,`M (abrace2mtype $3)) }  
  | FUNNAME COLON FORALL error { errr $3 "Expected quantifer (e.g., <a,'b,@c>) after 'forall'." }
  | FUNNAME COLON FORALL LT error GT { errr $3 "Expected ','-separated list of type variables (x/'x/@x/!x) between '<' and '>'." }
  | FUNNAME COLON FORALL LT netyvarlist GT DOT error { errr $7 "Expected data-level type after '.' here." }
  | FUNNAME COLON FORALL LT netyvarlist GT DOT error DBLSEMI { errr $7 "Expected data-level type after '.' here." }
  | FUNNAME COLON FORALL LT netyvarlist GT DOT ambig DBLSEMI { ($1,`P (Poly ($5,ambigmtype $8))) }
  | FUNNAME COLON FORALL LT netyvarlist GT DOT ambig_brace DBLSEMI { ($1,`P (Poly ($5,abrace2mtype $8))) }

toplet:
  | topsig FUNNAME eqpats expression 
    { namecheck $1 $2; (fst $1,(TopExp ($2,$1,$3,$4))) }
  | topsig FUNNAME eqpats ambig 
    { namecheck $1 $2; (fst $1,(TopExp ($2,$1,$3, ambigexp $4))) }
  | topsig linchan LARROW FUNNAME eqpats process
    { namecheck $1 $4; (fst $1,(TopMon ($4,$1,$5,$2,$6,[]))) }
  | topsig linchan LARROW FUNNAME tailpats chanlist EQUALS process
    { namecheck $1 $4; (fst $1,(TopMon ($4,$1,$5,$2,$8,$6))) }
  | topsig UNDERSCORE LARROW FUNNAME eqpats process
    { namecheck $1 $4; (fst $1,(TopDet ($4,$1,$5,$2,$6,[]))) }
  | topsig UNDERSCORE LARROW FUNNAME tailpats chanlist EQUALS process
    { namecheck $1 $4; (fst $1,(TopDet ($4,$1,$5,$2,$8,$6))) }

/* 
The modifier pure mean it may allow atomic expressions, (pure)
applications, infixes, monops, but not if, let, fun, or case
*/

expression:
  | or_exp				{ $1 }
  | pure_or_exp     { $1 }

or_exp:
  | and_exp		    { $1 }
  | pure_or_exp OR and_exp  { Bin ((locE $1),Or,$1,$3) }
  | ambig OR and_exp        { Bin ((ambigl $1),Or,ambigexp $1,$3) }

and_exp:
  | rel_exp		      { $1 }
  | pure_and_exp AND rel_exp  { Bin ((locE $1),And,$1,$3) }
  | ambig AND rel_exp         { Bin ((ambigl $1),And,ambigexp $1,$3) }

rel_exp:
  | rel_exp_lt     { $1 }
  | rel_exp_equals { $1 }
  | rel_exp_gt     { $1 }
  | rel_exp_leq    { $1 }
  | rel_exp_geq    { $1 }
  | cons_exp	     			{ $1 }

rel_exp_lt:
  | pure_rel_exp LT cons_exp		{ Bin ((locE $1),Less,$1,$3) }
  | ambig LT cons_exp		        { Bin ((ambigl $1),Less,ambigexp $1,$3) }

rel_exp_equals:
  | pure_rel_exp EQUALS cons_exp	{ Bin ((locE $1),Eq,$1,$3) }
  | ambig EQUALS cons_exp	        { Bin ((ambigl $1),Eq,ambigexp $1,$3) }

rel_exp_gt:
  | pure_rel_exp GT cons_exp            { Bin ((locE $1),GT,$1,$3) }
  | ambig GT cons_exp                   { Bin ((ambigl $1),GT,ambigexp $1,$3) }

rel_exp_leq:
  | pure_rel_exp LEQ cons_exp		{ Bin ((locE $1),LE,$1,$3) }
  | ambig LEQ cons_exp		        { Bin ((ambigl $1),LE,ambigexp $1,$3) }

rel_exp_geq:
  | pure_rel_exp GEQ cons_exp		{ Bin ((locE $1),GE,$1,$3) }
  | ambig GEQ cons_exp		        { Bin ((ambigl $1),GE,ambigexp $1,$3) }

cons_exp:
  | pure_add_exp DCOLON cons_exp	{ Sat((locE $1),"::",[$1;$3]) }
  | ambig DCOLON cons_exp	        { Sat((ambigl $1),"::",[ambigexp $1;$3]) }
  | add_exp				{ $1 }

add_exp:
  | add_exp_plus    { $1 }
  | add_exp_minus   { $1 }
  | add_exp_dplus   { $1 }
  | add_exp_dminus  { $1 }
  | add_exp_carat   { $1 }
  | mult_exp        { $1 }

add_exp_plus:
  | pure_add_exp PLUS mult_exp		{ Bin((locE $1),Add,$1,$3) }
  | ambig PLUS mult_exp		        { Bin((ambigl $1),Add,ambigexp $1,$3) }

add_exp_minus:
  | pure_add_exp MINUS mult_exp		{ Bin((locE $1),Sub,$1,$3) }
  | ambig MINUS mult_exp		{ Bin((ambigl $1),Sub,ambigexp $1,$3) }

add_exp_dplus:
  | pure_add_exp DPLUS mult_exp		{ Bin((locE $1),FAdd,$1,$3) }
  | ambig DPLUS mult_exp		{ Bin((ambigl $1),FAdd,ambigexp $1,$3) }

add_exp_dminus:
  | pure_add_exp DMINUS mult_exp	{ Bin((locE $1),FSub,$1,$3) }
  | ambig DMINUS mult_exp	        { Bin((ambigl $1),FSub,ambigexp $1,$3) }

add_exp_carat:
  | pure_add_exp CARAT mult_exp	        { Bin((locE $1),Concat,$1,$3) }
  | ambig CARAT mult_exp	        { Bin((ambigl $1),Concat,ambigexp $1,$3) }

mult_exp:
  | mult_exp_times   { $1 }
  | mult_exp_div     { $1 }
  | mult_exp_dtimes  { $1 }
  | mult_exp_ddiv    { $1 }
  | expo_exp	     { $1 }

mult_exp_times:
  | pure_mult_exp TIMES expo_exp 	{ Bin((locE $1),Mul,$1,$3) }
  | ambig TIMES expo_exp 	        { Bin((ambigl $1),Mul,ambigexp $1,$3) }

mult_exp_div:
  | pure_mult_exp DIV expo_exp 		{ Bin((locE $1),Div,$1,$3) }
  | ambig  DIV expo_exp 		{ Bin((ambigl $1),Div,ambigexp $1,$3) }

mult_exp_dtimes:
  | pure_mult_exp DTIMES expo_exp 	{ Bin((locE $1),FMul,$1,$3) }
  | ambig DTIMES expo_exp 	        { Bin((ambigl $1),FMul,ambigexp $1,$3) }

mult_exp_ddiv:
  | pure_mult_exp DDIV expo_exp 	{ Bin((locE $1),FDiv,$1,$3) }
  | ambig DDIV expo_exp 	        { Bin((ambigl $1),FDiv,ambigexp $1,$3) }

expo_exp:
  | ambig EXP expo_exp                { Bin ((ambigl $1),Exp,ambigexp $1,$3) }
  | app_exp                           { $1 }

app_exp:
  | if_let_fun_case_exp                           { $1 }
  | ambig  if_let_fun_case_exp                    { App((ambigl $1),ambigexp $1,$2) }

if_let_fun_case_exp:
  | LET FUNNAME colonpats ambig EQUALS expression IN expression
      { Let($1,`M (ambigmtype $4),$2,$3,$6,$8) }
  | LET FUNNAME colonpats ambig_brace EQUALS expression IN expression
      { Let($1,`M (abrace2mtype $4),$2,$3,$6,$8) }
  | LET FUNNAME colonpats ambig EQUALS expression IN ambig
      { Let($1,`M (ambigmtype $4),$2,$3,$6,ambigexp $8) }
  | LET FUNNAME colonpats ambig_brace EQUALS expression IN ambig
      { Let($1,`M (abrace2mtype $4),$2,$3,$6,ambigexp $8) }
  | LET FUNNAME colonpats ambig EQUALS ambig IN expression
      { Let($1,`M (ambigmtype $4),$2,$3,ambigexp $6,$8) }
  | LET FUNNAME colonpats ambig_brace EQUALS ambig IN expression
      { Let($1,`M (abrace2mtype $4),$2,$3,ambigexp $6,$8) }
  | LET FUNNAME colonpats ambig EQUALS ambig IN ambig
      { Let($1,`M (ambigmtype $4),$2,$3,ambigexp $6,ambigexp $8) }
  | LET FUNNAME colonpats ambig_brace EQUALS ambig IN ambig
      { Let($1,`M (abrace2mtype $4),$2,$3,ambigexp $6,ambigexp $8) }
  | FUN arrowpats expression  { match $2 with 
                                    | [] -> errr $1 "No arguments to 'function'";
                                    | hd::tl -> Fun ($1,hd,tl,$3)}
  | FUN arrowpats ambig  { match $2 with 
                                    | [] -> errr $1 "No arguments to 'function'";
                                    | hd::tl -> Fun ($1,hd,tl,ambigexp $3)}
  | IF expression THEN expression ELSE expression { If($1,$2,$4,$6) }
  | IF expression THEN expression ELSE ambig      { If($1,$2,$4,ambigexp $6) }
  | IF expression THEN ambig ELSE expression	  { If($1,$2,ambigexp $4,$6) }
  | IF expression THEN ambig ELSE ambig	          { If($1,$2,ambigexp $4,ambigexp $6) }
  | IF ambig THEN expression ELSE expression      { If($1,ambigexp $2,$4,$6) }
  | IF ambig THEN expression ELSE ambig           { If($1,ambigexp $2,$4,ambigexp $6) }
  | IF ambig THEN ambig ELSE expression	          { If($1,ambigexp $2,ambigexp $4,$6) }
  | IF ambig THEN ambig ELSE ambig	          { If($1,ambigexp $2,ambigexp $4,ambigexp $6) }
  | CASE expression OF matches	{ Case($1,$2,$4) }
  | CASE ambig OF matches	{ Case($1,ambigexp $2,$4) }

matches:
  | onematch { SM.singleton (fst $1) (snd $1) }
  | onematch matches { SM.add $2 (fst $1) (snd $1) }

onematch: 
  | PIPE TYNAME arrowpats expression { (snd $2,($3,$4)) }
  | PIPE TYNAME arrowpats ambig { (snd $2,($3,ambigexp $4)) }
  | PIPE LBRAC RBRAC ARROW expression { ("[]",([],$5)) }
  | PIPE LBRAC RBRAC ARROW ambig { ("[]",([],ambigexp $5)) }
  | PIPE patvar DCOLON patvar ARROW expression { ("::",([$2;$4],$6)) }
  | PIPE patvar DCOLON patvar ARROW ambig { ("::",([$2;$4],ambigexp $6)) }
  | PIPE LPAREN patvar COMMA patvar RPAREN ARROW expression { (",",([$3;$5],$8)) }
  | PIPE LPAREN patvar COMMA patvar RPAREN ARROW ambig { (",",([$3;$5],ambigexp $8)) }

patvar:
  | UNDERSCORE { ($1,priv_name ()) }
  | FUNNAME { $1 }

pure_or_exp:
  | pure_and_exp   			{ $1 }
  | pure_or_exp OR pure_and_exp		{ Bin ((locE $1),Or,$1,$3) }
  | pure_or_exp OR ambig		{ Bin ((locE $1),Or,$1,ambigexp $3) }
  | ambig OR ambig                      { Bin ((ambigl $1),Or,ambigexp $1,ambigexp $3) }

pure_and_exp:
  | pure_rel_exp	     	  { $1 }
  | pure_and_exp AND pure_rel_exp { Bin ((locE $1),And,$1,$3) }
  | pure_and_exp AND ambig	  { Bin ((locE $1),And,$1,ambigexp $3) }
  | ambig AND ambig               { Bin ((ambigl $1),And,ambigexp $1,ambigexp $3) }

pure_rel_exp:
  | pure_rel_exp_lt     { $1 }
  | pure_rel_exp_equals { $1 }
  | pure_rel_exp_gt     { $1 }
  | pure_rel_exp_geq    { $1 }
  | pure_rel_exp_leq    { $1 }
  | pure_cons_exp	{ $1 }

pure_rel_exp_lt:
  | pure_rel_exp LT pure_cons_exp	{ Bin ((locE $1),Less,$1,$3) }
  | pure_rel_exp LT ambig               { Bin ((locE $1),Less,$1,ambigexp $3) }
  | ambig LT ambig                      { Bin ((ambigl $1),Less,ambigexp $1,ambigexp $3) }

pure_rel_exp_equals:
  | pure_rel_exp EQUALS pure_cons_exp	{ Bin ((locE $1),Eq,$1,$3) }
  | pure_rel_exp EQUALS ambig     	{ Bin ((locE $1),Eq,$1,ambigexp $3) }
  | ambig EQUALS ambig          	{ Bin ((ambigl $1),Eq,ambigexp $1,ambigexp $3) }

pure_rel_exp_gt:
  | pure_rel_exp GT pure_cons_exp	{ Bin ((locE $1),GT,$1,$3) }
  | pure_rel_exp GT ambig        	{ Bin ((locE $1),GT,$1,ambigexp $3) }
  | ambig GT ambig                   	{ Bin ((ambigl $1),GT,ambigexp $1,ambigexp $3) }

pure_rel_exp_geq:
  | pure_rel_exp GEQ pure_cons_exp	{ Bin ((locE $1),GE,$1,$3) }
  | pure_rel_exp GEQ ambig	        { Bin ((locE $1),GE,$1,ambigexp $3) }
  | ambig GEQ ambig	                { Bin ((ambigl $1),GE,ambigexp $1,ambigexp $3) }

pure_rel_exp_leq:
  | pure_rel_exp LEQ pure_cons_exp	{ Bin ((locE $1),LE,$1,$3) }
  | pure_rel_exp LEQ ambig      	{ Bin ((locE $1),LE,$1,ambigexp $3) }
  | ambig LEQ ambig             	{ Bin ((ambigl $1),LE,ambigexp $1,ambigexp $3) }

pure_cons_exp:
  | pure_add_exp			{ $1 }
  | pure_add_exp DCOLON pure_cons_exp   { Sat((locE $1),"::",[$1;$3]) }
  | pure_add_exp DCOLON ambig           { Sat((locE $1),"::",[$1;ambigexp $3]) }
  | ambig DCOLON ambig                  { Sat((ambigl $1),"::",[ambigexp $1;ambigexp $3]) }

pure_add_exp:
  | pure_add_exp_plus     { $1 }
  | pure_add_exp_minus     { $1 }
  | pure_add_exp_dplus     { $1 }
  | pure_add_exp_dminus     { $1 }
  | pure_add_exp_carat  { $1 }
  | pure_mult_exp			{ $1 }

pure_add_exp_plus:
  | pure_add_exp PLUS pure_mult_exp	{ Bin((locE $1),Add,$1,$3) }
  | pure_add_exp PLUS ambig	        { Bin((locE $1),Add,$1,ambigexp $3) }
  | ambig PLUS ambig	                { Bin((ambigl $1),Add,ambigexp $1,ambigexp $3) }

pure_add_exp_minus:
  | pure_add_exp MINUS pure_mult_exp	{ Bin((locE $1),Sub,$1,$3) }
  | pure_add_exp MINUS ambig    	{ Bin((locE $1),Sub,$1,ambigexp $3) }
  | ambig MINUS ambig           	{ Bin((ambigl $1),Sub,ambigexp $1,ambigexp $3) }

pure_add_exp_dplus:
  | pure_add_exp DPLUS pure_mult_exp	{ Bin((locE $1),FAdd,$1,$3) }
  | pure_add_exp DPLUS ambig	        { Bin((locE $1),FAdd,$1,ambigexp $3) }
  | ambig DPLUS ambig	                { Bin((ambigl $1),FAdd,ambigexp $1,ambigexp $3) }

pure_add_exp_dminus:
  | pure_add_exp DMINUS pure_mult_exp	{ Bin((locE $1),FSub,$1,$3) }
  | pure_add_exp DMINUS ambig    	{ Bin((locE $1),FSub,$1,ambigexp $3) }
  | ambig DMINUS ambig           	{ Bin((ambigl $1),FSub,ambigexp $1,ambigexp $3) }

pure_add_exp_carat:
  | pure_add_exp CARAT pure_mult_exp    { Bin((locE $1),Concat,$1,$3) }
  | pure_add_exp CARAT ambig            { Bin((locE $1),Concat,$1,ambigexp $3) }
  | ambig CARAT ambig                   { Bin((ambigl $1),Concat,ambigexp $1,ambigexp $3) }

pure_mult_exp:
  | pure_mult_exp_times     { $1 }
  | pure_mult_exp_div       { $1 }
  | pure_mult_exp_dtimes    { $1 }
  | pure_mult_exp_ddiv      { $1 }
  | pure_expo_exp	       		{ $1 }

pure_mult_exp_times:
  | pure_mult_exp TIMES pure_expo_exp 	{ Bin((locE $1),Mul,$1,$3) }
  | pure_mult_exp TIMES ambig 	        { Bin((locE $1),Mul,$1,ambigexp $3) }

pure_mult_exp_div:
  | pure_mult_exp DIV pure_expo_exp 	{ Bin((locE $1),Div,$1,$3) }
  | pure_mult_exp DIV ambig      	{ Bin((locE $1),Div,$1,ambigexp $3) }
  | ambig DIV ambig             	{ Bin((ambigl $1),Div,ambigexp $1,ambigexp $3) }

pure_mult_exp_dtimes:
  | pure_mult_exp DTIMES pure_expo_exp 	{ Bin((locE $1),FMul,$1,$3) }
  | pure_mult_exp DTIMES ambig 	        { Bin((locE $1),FMul,$1,ambigexp $3) }
  | ambig DTIMES ambig                  { Bin((ambigl $1),FMul,ambigexp $1,ambigexp $3) }

pure_mult_exp_ddiv:
  | pure_mult_exp DDIV pure_expo_exp 	{ Bin((locE $1),FDiv,$1,$3) }
  | pure_mult_exp DDIV ambig      	{ Bin((locE $1),FDiv,$1,ambigexp $3) }
  | ambig DDIV ambig             	{ Bin((ambigl $1),FDiv,ambigexp $1,ambigexp $3) }

pure_expo_exp:
  | ambig EXP pure_expo_exp  { Bin((ambigl $1),Exp,ambigexp $1,$3) }
  | ambig EXP ambig          { Bin((ambigl $1),Exp,ambigexp $1,ambigexp $3) }

atomic_expression:
    constant_expression         { Con ((fst $1),snd $1) }
  | LPAREN expression RPAREN    { $2 }
  | LPAREN expression COMMA expression RPAREN    { Sat (locE $2,",",[$2;$4]) }
  | LPAREN expression COMMA ambig RPAREN    { Sat (locE $2,",",[$2;ambigexp $4]) }
  | LPAREN ambig COMMA expression RPAREN    { Sat (ambigl $2,",",[ambigexp $2;$4]) }
  | list_expression		{ $1 }
  | linchan LARROW LBRACE process_nf RBRACE 
    { Monad((fst $1),Some $1,$4,[]) }
  | linchan LARROW ambig_brace 
    { Monad((fst $1),Some $1,abrace2proc $3,[]) }
  | shrchan LARROW LBRACE process_nf RBRACE 
    { Monad((fst $1),Some $1,$4,[]) }
  | shrchan LARROW ambig_brace
    { Monad((fst $1),Some $1,abrace2proc $3,[]) }
  | UNDERSCORE LARROW LBRACE process_nf RBRACE { Monad($1,None,$4,[]) }
  | UNDERSCORE LARROW ambig_brace { Monad($1,None,abrace2proc $3,[]) }
  | UNDERSCORE LARROW LBRACE process_nf RBRACE TAIL chanlist { Monad($1,None,$4,$7) }
  | UNDERSCORE LARROW ambig_brace TAIL chanlist { Monad($1,None,abrace2proc $3,$5) }
  | linchan LARROW LBRACE process_nf RBRACE TAIL chanlist 
       { Monad((fst $1),Some $1,$4,$7) }
  | linchan LARROW ambig_brace TAIL chanlist 
       { Monad((fst $1),Some $1,abrace2proc $3,$5) }
  | shrchan LARROW LBRACE process_nf RBRACE TAIL chanlist 
    { Monad((fst $1),Some $1,$4,$7) }
  | shrchan LARROW ambig_brace TAIL chanlist 
    { Monad((fst $1),Some $1,abrace2proc $3,$5) }
  | LBRAC RBRAC                       { Sat($1,"[]",[]) }
  | LT expression COLON ambig GT 
      { Cast ((locE $2),$2,ambigmtype $4) }
  | LT expression COLON ambig_brace GT 
      { Cast ((locE $2),$2,abrace2mtype $4) }
  | LT ambig COLON ambig GT 
      { Cast ((ambigl $2),ambigexp $2,ambigmtype $4) }
  | LT ambig COLON ambig_brace GT 
      { Cast ((ambigl $2),ambigexp $2,abrace2mtype $4) }
  | POLY polytail  { PolyApp(fst $1,$1,$2) }

polytail:
  | GT                         { [] }
  | sessiontype GT             { [`S $1] }
  | shrchan GT                 { [`S (chan2svar $1)] }
  | linchan GT                 { [`S (chan2svar $1)] }
  | ambig GT                   { [`A $1] }
  | addtail GT                 { [`S ($1 Linear)] }
  | sessiontype COMMA polytail { (`S $1) :: $3 }
  | shrchan COMMA polytail     { (`S (chan2svar $1)) :: $3 }
  | linchan COMMA polytail     { (`S (chan2svar $1)) :: $3 }
  | ambig COMMA polytail       { (`A $1) :: $3 }
  | addtail COMMA polytail     { (`S ($1 Linear)) :: $3 }

list_expression:
    LBRAC list_contents			{ $2 }
 
list_contents:
    | expression SEMI list_contents  { Sat(locE $1,"::",[$1;$3]) }
    | ambig SEMI list_contents     { Sat(ambigl $1,"::",[ambigexp $1;$3]) }
    | expression SEMI ambig RBRAC  { Sat(locE $1,"::",[$1;
                                           Sat(ambigl $3,"::",[ambigexp $3;
                                                   Sat($4,"[]",[])])]) }
    | ambig SEMI ambig RBRAC        { Sat(ambigl $1,"::",[ambigexp $1;
                                           Sat(ambigl $3,"::",[ambigexp $3;
                                                   Sat($4,"[]",[])])]) }
    | expression RBRAC               { Sat(locE $1,"::",[$1;Sat($2,"[]",[])]) }

constant_expression:
  | FLOAT			{ (fst $1,Float (snd $1)) }
  | STRING			{ (fst $1,String (snd $1)) }

chanlist:
  | linchan { [$1] }
  | shrchan { [$1] }
  | linchan chanlist { $1::$2 }
  | shrchan chanlist { $1::$2 }

linchan:
  | LINCHAN { (fst $1, Lin (snd $1)) }
  | AFFCHAN { (fst $1, Aff (snd $1)) }

shrchan:
  | SHRCHAN { (fst $1, Shr (snd $1)) }

matchesP:
  | onematchP { let (c,m) = $1 in SM.singleton c m  }
  | onematchP matchesP { let (c,m) = $1 in SM.add $2 c m }

onematchP: 
  | PIPE TYNAME arrowpats process { (snd $2,($3,$4)) }
  | PIPE LBRAC RBRAC ARROW process { ("[]",([],$5)) }
  | PIPE patvar DCOLON patvar ARROW process { ("::",([$2;$4],$6)) }


process:
  | /* empty */ { Exit {lnum = -1; cnum = -1} }
  | linchan LARROW SERVICE TYNAME SEMI process { Service(fst $1,$1,$4,$6) }
  | REGISTER TYNAME linchan SEMI process { Register($1,$2,$3,$5) }
  | ABORT { Abort $1 }
  | FUNNAME LARROW INPUT linchan SEMI process { InD ($3,$1,$4,$6) }
  | UNDERSCORE LARROW INPUT linchan SEMI process { InD ($3,($1,priv_name ()),$4,$6) }
  | OUTPUT linchan expression SEMI process { OutD ($1,$2,$3,$5) }
  | OUTPUT linchan ambig SEMI process { OutD ($1,$2,ambigexp $3,$5) }
  | linchan LARROW INPUT linchan SEMI process { InC ((fst $1), $1,$4,$6) }
  | linchan LARROW INPUT shrchan SEMI process { InC ((fst $1), $1,$4,$6) }
  | shrchan LARROW INPUT linchan SEMI process { InC ((fst $1), $1,$4,$6) }
  | shrchan LARROW INPUT shrchan SEMI process { InC ((fst $1), $1,$4,$6) }
  | OUTPUT linchan LPAREN linchan LARROW process RPAREN SEMI process 
           { OutC ($1,$2, $4, $6, $9) }
  | OUTPUT linchan linchan SEMI process { Throw ($1,$2,$3,$5) }
  | linchan LARROW OUTPUT linchan SEMI process { ShftUpL (fst $1,$1,$4,$6) }
  | linchan LARROW OUTPUT shrchan SEMI process { ShftUpL (fst $1,$1,$4,$6) }
  | OUTPUT linchan LPAREN linchan LARROW process RPAREN { ShftDwR ($1,$2,$4,$6) }
  | OUTPUT linchan LPAREN shrchan LARROW process RPAREN { ShftDwR ($1,$2,$4,$6) }
  | linchan LARROW linchan {Fwd((fst $1),$1,$3) }
  | linchan LARROW linchan SEMI error { errr $4 "Forwarding terminates a process. Didn't expect a lone ';' here." }
  | CLOSE linchan { Close ($1,$2) }
  | CLOSE error { errr $1 "Expected a channel argument to 'close'" }
  | CLOSE linchan SEMI error { errr $3 "'close' terminates a process. Didn't expect a lone ';' here." }
  | CLOSE { Exit $1 }
  | WAIT linchan SEMI process { Wait ($1,$2,$4) }
  | linchan LARROW expression SEMI process 
    { Bind ((fst $1),$1,$3,[],$5) }
  | linchan LARROW ambig SEMI process 
    { Bind ((fst $1),$1,ambigexp $3,[],$5) }
  | shrchan LARROW expression SEMI process
    { Bind ((fst $1),$1,$3,[],$5) }
  | shrchan LARROW ambig SEMI process
    { Bind ((fst $1),$1,ambigexp $3,[],$5) }
  | linchan LARROW expression TAIL chanlist SEMI process 
    { Bind ((fst $1),$1,$3,$5,$7) }
  | linchan LARROW ambig TAIL chanlist SEMI process 
    { Bind ((fst $1),$1,ambigexp $3,$5,$7) }
  | shrchan LARROW expression TAIL chanlist SEMI process 
    { Bind ((fst $1) ,$1,$3,$5,$7) }
  | shrchan LARROW ambig TAIL chanlist SEMI process 
    { Bind ((fst $1) ,$1,ambigexp $3,$5,$7) }
  | linchan LARROW expression { TailBind (fst $1,$1,$3,[]) }
  | linchan LARROW ambig { TailBind (fst $1,$1,ambigexp $3,[]) }
  | linchan LARROW expression TAIL chanlist { TailBind (fst $1,$1,$3,$5) }
  | linchan LARROW ambig TAIL chanlist { TailBind (fst $1,$1,ambigexp $3,$5) }
  | UNDERSCORE LARROW expression SEMI process { Detached ($1,$3,[],$5) }
  | UNDERSCORE LARROW ambig SEMI process { Detached ($1,ambigexp $3,[],$5) }
  | UNDERSCORE LARROW expression TAIL chanlist SEMI process { Detached ($1,$3,$5,$7) }
  | UNDERSCORE LARROW ambig TAIL chanlist SEMI process { Detached ($1,ambigexp $3,$5,$7) }
  | LPAREN process RPAREN { $2 }
  | CASE expression OF matchesP { CaseP ($1,$2,$4) }
  | CASE ambig OF matchesP { CaseP ($1,ambigexp $2,$4) }
  | IF expression THEN process ELSE process { IfP ($1,$2,$4,$6) }
  | IF ambig THEN process ELSE process { IfP ($1,ambigexp $2,$4,$6) }
  | linchan DOT FUNNAME SEMI process { Internal (fst $1,$1,$3,$5) }
  | CASE linchan OF { External ($1, $2, LM.empty) }
  | CASE linchan OF extcases { External ($1,$2,$4)  }
  | expression SEMI process { Seq (locE $1,$1,$3) }
  | ambig SEMI process { Seq (ambigl $1,ambigexp $1,$3) }
  | LET FUNNAME colonpats ambig EQUALS expression SEMI process 
        { LetP ($1,`M (ambigmtype $4),$2,$3,$6,$8) }
  | LET FUNNAME colonpats ambig_brace EQUALS expression SEMI process 
        { LetP ($1,`M (abrace2mtype $4),$2,$3,$6,$8) }
  | LET FUNNAME colonpats ambig EQUALS ambig SEMI process 
        { LetP ($1,`M (ambigmtype $4),$2,$3,ambigexp $6,$8) }
  | LET FUNNAME colonpats ambig_brace EQUALS ambig SEMI process 
        { LetP ($1,`M (abrace2mtype $4),$2,$3,ambigexp $6,$8) }
  | OUTPUT linchan LT sessiontype GT SEMI process { OutTy ($1,$2,$4,$7) }
  | OUTPUT linchan LT linchan GT SEMI process { OutTy ($1,$2,chan2svar $4,$7) }
  | OUTPUT linchan LT shrchan GT SEMI process { OutTy ($1,$2,chan2svar $4,$7) }
  | OUTPUT linchan LT ambig GT SEMI process { OutTy ($1,$2,ambigstype $4,$7) }
  | OUTPUT linchan LT addtail GT SEMI process { OutTy ($1,$2,$4 Linear,$7) } /* TODO Get rid of the application here */
  | LT linchan GT LARROW INPUT linchan SEMI process {  InTy (fst $2,chan2tyvar $2,$6,$8) }
  | LT shrchan GT LARROW INPUT linchan SEMI process {  InTy (fst $2,chan2tyvar $2,$6,$8) }


/* This is needed to differentiate { 'a <- 'a } the type and { 'a <- 'a } the forwarding */
process_nf:
  | /* empty */ { Exit {lnum = -1; cnum = -1} }
  | linchan LARROW SERVICE TYNAME SEMI process { Service(fst $1,$1,$4,$6) }
  | REGISTER TYNAME linchan SEMI process { Register($1,$2,$3,$5) }
  | ABORT { Abort $1 }
  | FUNNAME LARROW INPUT linchan SEMI process { InD ($3,$1,$4,$6) }
  | UNDERSCORE LARROW INPUT linchan SEMI process { InD ($3,($1,priv_name ()),$4,$6) }
  | OUTPUT linchan expression SEMI process { OutD ($1,$2,$3,$5) }
  | OUTPUT linchan ambig SEMI process { OutD ($1,$2,ambigexp $3,$5) }
  | linchan LARROW INPUT linchan SEMI process { InC ((fst $1), $1,$4,$6) }
  | linchan LARROW INPUT shrchan SEMI process { InC ((fst $1), $1,$4,$6) }
  | shrchan LARROW INPUT linchan SEMI process { InC ((fst $1), $1,$4,$6) }
  | shrchan LARROW INPUT shrchan SEMI process { InC ((fst $1), $1,$4,$6) }
  | OUTPUT linchan LPAREN linchan LARROW process RPAREN SEMI process 
           { OutC ($1,$2, $4, $6, $9) }
  | OUTPUT linchan linchan SEMI process { Throw ($1,$2,$3,$5) }
  | linchan LARROW OUTPUT linchan SEMI process { ShftUpL (fst $1,$1,$4,$6) }
  | linchan LARROW OUTPUT shrchan SEMI process { ShftUpL (fst $1,$1,$4,$6) }
  | OUTPUT linchan LPAREN linchan LARROW process RPAREN { ShftDwR ($1,$2,$4,$6) }
  | OUTPUT linchan LPAREN shrchan LARROW process RPAREN { ShftDwR ($1,$2,$4,$6) }
  | CLOSE linchan { Close ($1,$2) }
  | CLOSE error { errr $1 "Expected a channel argument to 'close'" }
  | CLOSE linchan SEMI error { errr $3 "'close' terminates a process. Didn't expect a lone ';' here." }
  | CLOSE { Exit $1 }
  | CLOSE SEMI error { errr $2 "'close' terminates a process. Didn't expect a lone ';' here." }
  | WAIT linchan SEMI process { Wait ($1,$2,$4) }
  | linchan LARROW expression SEMI process 
    { Bind ((fst $1),$1,$3,[],$5) }
  | linchan LARROW ambig SEMI process 
    { Bind ((fst $1),$1,ambigexp $3,[],$5) }
  | shrchan LARROW expression SEMI process
    { Bind ((fst $1),$1,$3,[],$5) }
  | shrchan LARROW ambig SEMI process
    { Bind ((fst $1),$1,ambigexp $3,[],$5) }
  | linchan LARROW expression TAIL chanlist SEMI process 
    { Bind ((fst $1),$1,$3,$5,$7) }
  | linchan LARROW ambig TAIL chanlist SEMI process 
    { Bind ((fst $1),$1,ambigexp $3,$5,$7) }
  | shrchan LARROW expression TAIL chanlist SEMI process 
    { Bind ((fst $1) ,$1,$3,$5,$7) }
  | shrchan LARROW ambig TAIL chanlist SEMI process 
    { Bind ((fst $1) ,$1,ambigexp $3,$5,$7) }
  | linchan LARROW expression { TailBind (fst $1,$1,$3,[]) }
  | linchan LARROW ambig { TailBind (fst $1,$1,ambigexp $3,[]) }
  | linchan LARROW expression TAIL chanlist { TailBind (fst $1,$1,$3,$5) }
  | linchan LARROW ambig TAIL chanlist { TailBind (fst $1,$1,ambigexp $3,$5) }
  | UNDERSCORE LARROW expression SEMI process { Detached ($1,$3,[],$5) }
  | UNDERSCORE LARROW ambig SEMI process { Detached ($1,ambigexp $3,[],$5) }
  | UNDERSCORE LARROW expression TAIL chanlist SEMI process { Detached ($1,$3,$5,$7) }
  | UNDERSCORE LARROW ambig TAIL chanlist SEMI process { Detached ($1,ambigexp $3,$5,$7) }
  | LPAREN process RPAREN { $2 }
  | CASE expression OF matchesP { CaseP ($1,$2,$4) }
  | CASE ambig OF matchesP { CaseP ($1,ambigexp $2,$4) }
  | IF expression THEN process ELSE process { IfP ($1,$2,$4,$6) }
  | IF ambig THEN process ELSE process { IfP ($1,ambigexp $2,$4,$6) }
  | linchan DOT FUNNAME SEMI process { Internal (fst $1,$1,$3,$5) }
  | CASE linchan OF { External ($1, $2, LM.empty) }
  | CASE linchan OF extcases { External ($1,$2,$4)  }
  | expression SEMI process { Seq (locE $1,$1,$3) }
  | ambig SEMI process { Seq (ambigl $1,ambigexp $1,$3) }
  | LET FUNNAME colonpats ambig EQUALS expression SEMI process 
        { LetP ($1,`M (ambigmtype $4),$2,$3,$6,$8) }
  | LET FUNNAME colonpats ambig_brace EQUALS expression SEMI process 
        { LetP ($1,`M (abrace2mtype $4),$2,$3,$6,$8) }
  | LET FUNNAME colonpats ambig EQUALS ambig SEMI process 
        { LetP ($1,`M (ambigmtype $4),$2,$3,ambigexp $6,$8) }
  | LET FUNNAME colonpats ambig_brace EQUALS ambig SEMI process 
        { LetP ($1,`M (abrace2mtype $4),$2,$3,ambigexp $6,$8) }
  | OUTPUT linchan LT sessiontype GT SEMI process { OutTy ($1,$2,$4,$7) }
  | OUTPUT linchan LT linchan GT SEMI process { OutTy ($1,$2,chan2svar $4,$7) }
  | OUTPUT linchan LT shrchan GT SEMI process { OutTy ($1,$2,chan2svar $4,$7) }
  | OUTPUT linchan LT ambig GT SEMI process { OutTy ($1,$2,ambigstype $4,$7) }
  | OUTPUT linchan LT addtail GT SEMI process { OutTy ($1,$2,$4 Linear,$7) } /* TODO Get rid of the application here */
  | LT linchan GT LARROW INPUT linchan SEMI process {  InTy (fst $2,chan2tyvar $2,$6,$8) }
  | LT shrchan GT LARROW INPUT linchan SEMI process {  InTy (fst $2,chan2tyvar $2,$6,$8) }

extcases:
  | PIPE extcase { LM.singleton (fst $2) (snd $2) }
  | PIPE extcase extcases { if LM.mem $3 (fst $2)
                            then errr (fst (fst $2)) ("Duplicate case "^string_of_label (fst $2))
                            else LM.add $3 (fst $2) (snd $2) }

extcase:
  | FUNNAME ARROW process { ($1,$3) }

monotype_atom:
  | LBRACE error { errr $1 "Expected monad type here. E.g., { 1 <- Stream a }" }
  | LBRACE error RBRACE { errr $1 "Expected monad type here. E.g., { 1 <- Stream a }" }
  | LBRACE error LARROW sessiontype RBRACE { errr $3 "Expected session type before '<-' here." }
  | LBRACE error LARROW linchan RBRACE { errr $3 "Expected session type before '<-' here." }
  | LBRACE error LARROW shrchan RBRACE { errr $3 "Expected session type before '<-' here." }
  | LBRACE error LARROW ambig RBRACE { errr $3 "Expected session type before '<-' here." }
  | LBRACE error LARROW sestypes_ne RBRACE { errr $3 "Expected session type before '<-' here." }
  | LBRACE error LARROW addtail RBRACE { errr $3 "Expected session type before '<-' here." }
  | monadprefix LARROW error RBRACE { errr $2 ("Expected (';' separated) list of session types "
                                              ^"after '<-' here.") }
  | LBRACE LARROW error RBRACE { errr $2 ("Expected (';' separated) list of session types "
                                              ^"after '<-' here.") }
  | DIAMOND monotype_atom { Comp ("<>",[$2]) }
  | monadprefix RBRACE { MonT ($1,[]) }
  | monadprefix LARROW sessiontype RBRACE { MonT($1,[$3]) }
  | monadprefix LARROW linchan RBRACE { MonT($1,[chan2svar $3]) }
  | monadprefix LARROW shrchan RBRACE { MonT($1,[chan2svar $3]) }
  | monadprefix LARROW sestypes_ne RBRACE { MonT($1,$3) }
  | monadprefix LARROW addtail RBRACE { MonT($1,[$3 Linear]) }
  | monadprefix LARROW ambig RBRACE { MonT($1,[ambigstype $3]) }
  | LBRACE RBRACE { MonT (None,[]) }
  | LBRACE LARROW sessiontype RBRACE { MonT (None,[$3]) }
  | LBRACE LARROW sestypes_ne RBRACE { MonT (None,$3) }
  | LBRACE LARROW addtail RBRACE { MonT (None,[$3 Linear]) }
  | LBRACE LARROW ambig RBRACE { MonT (None,[ambigstype $3]) }
  | LBRACE LARROW linchan RBRACE { MonT (None,[chan2svar $3]) }
  | LBRACE LARROW shrchan RBRACE { MonT (None,[chan2svar $3]) }
  | LBRACE linchan LARROW sestypes_ne RBRACE { MonT (Some (chan2svar $2),$4) }
  | LBRACE linchan LARROW sessiontype RBRACE { MonT (Some (chan2svar $2),[$4]) }
  | LBRACE linchan LARROW addtail RBRACE { MonT (Some (chan2svar $2),[$4 Linear]) }
  | LBRACE linchan LARROW ambig RBRACE { MonT (Some (chan2svar $2),[ambigstype $4]) }
  
monadprefix: 
  | LBRACE sessiontype { Some $2}
  | LBRACE ambig       { Some (ambigstype $2) }
  | LBRACE addtail     { Some ($2 Linear) }

sestypes_ne:
  | error SEMI sessiontype { errr $2 "Expected a session type before ';' here." }
  | error SEMI sestypes_ne { errr $2 "Expected a session type before ';' here." }
  | error SEMI addtail { errr $2 "Expected a session type before ';' here." }
  | error SEMI ambig { errr $2 "Expected a session type before ';' here." }
  | error SEMI linchan { errr $2 "Expected a session type before ';' here." }
  | error SEMI shrchan { errr $2 "Expected a session type before ';' here." }
  | sessiontype SEMI error { errr $2 "Expected a session type after ';' here." }
  | addtail SEMI error { errr $2 "Expected a session type after ';' here." }
  | ambig SEMI error { errr $2 "Expected a session type after ';' here." }
  | linchan SEMI error { errr $2 "Expected a session type after ';' here." }
  | shrchan SEMI error { errr $2 "Expected a session type after ';' here." }
  | sessiontype SEMI sessiontype { $1::[$3] }
  | sessiontype SEMI sestypes_ne { $1::$3 }
  | sessiontype SEMI addtail { $1::[$3 Linear] }
  | sessiontype SEMI ambig { $1::[ambigstype $3] }
  | sessiontype SEMI linchan { $1::[chan2svar $3] }
  | sessiontype SEMI shrchan { $1::[chan2svar $3] }
  | addtail SEMI sessiontype { ($1 Linear) :: [$3] }
  | addtail SEMI sestypes_ne { ($1 Linear) :: $3 }
  | addtail SEMI addtail { ($1 Linear)::[($3 Linear)] }
  | addtail SEMI ambig { ($1 Linear) :: [ambigstype $3] }
  | addtail SEMI linchan { ($1 Linear) :: [chan2svar $3] }
  | addtail SEMI shrchan { ($1 Linear) :: [chan2svar $3] }
  | ambig SEMI sessiontype    { (ambigstype $1) :: [$3] }
  | ambig SEMI sestypes_ne    { (ambigstype $1) :: $3 }
  | ambig SEMI addtail        { (ambigstype $1) :: [($3 Linear)] }
  | ambig SEMI ambig          { (ambigstype $1) :: [ambigstype $3] }
  | ambig SEMI linchan        { (ambigstype $1) :: [chan2svar $3] }
  | ambig SEMI shrchan        { (ambigstype $1) :: [chan2svar $3] }
  | linchan SEMI sessiontype    { (chan2svar $1) :: [$3] }
  | linchan SEMI sestypes_ne    { (chan2svar $1) :: $3 }
  | linchan SEMI addtail        { (chan2svar $1) :: [($3 Linear)] }
  | linchan SEMI ambig          { (chan2svar $1) :: [ambigstype $3] }
  | linchan SEMI linchan        { (chan2svar $1) :: [chan2svar $3] }
  | linchan SEMI shrchan        { (chan2svar $1) :: [chan2svar $3] }
  | shrchan SEMI sessiontype    { (chan2svar $1) :: [$3] }
  | shrchan SEMI sestypes_ne    { (chan2svar $1) :: $3 }
  | shrchan SEMI addtail        { (chan2svar $1) :: [($3 Linear)] }
  | shrchan SEMI ambig          { (chan2svar $1) :: [ambigstype $3] }
  | shrchan SEMI linchan        { (chan2svar $1) :: [chan2svar $3] }
  | shrchan SEMI shrchan        { (chan2svar $1) :: [chan2svar $3] }

sessiontype:
  | stype_atom { $1 }
  | wedge_types { $1 }
  | shoe_types { $1 }
  | AT error { errr $1 "Expected session type after '@' here." }
  | AT sessiontype { At $2 }
  | AT linchan { At (chan2svar $2) }
  | AT shrchan { At (chan2svar $2) }
  | AT ambig { At (ambigstype $2) }
  | AT addtail { At ($2 Linear) }
  | PRIME error { errr $1 "Expected session type after '\'' here." }
  | PRIME sessiontype { Prime $2 }
  | PRIME linchan { Prime (chan2svar $2) }
  | PRIME shrchan { Prime (chan2svar $2) }
  | PRIME ambig { Prime (ambigstype $2) }
  | PRIME addtail { Prime ($2 Linear) }
  | BANG error { errr $1 "Expected session type after '!' here." }
  | BANG sessiontype { Bang $2 }
  | BANG linchan { Bang (chan2svar $2) }
  | BANG shrchan { Bang (chan2svar $2) }
  | BANG ambig { Bang (ambigstype $2) }
  | BANG addtail { Bang ($2 Linear) }
  | FORALL linchan DOT error { errr $3 "Expected a session type after '.' here." }
  | FORALL linchan DOT sessiontype { Forall (Linear,chan2tyvar $2,$4) }
  | FORALL linchan DOT linchan { Forall (Linear,chan2tyvar $2,chan2svar $4) }
  | FORALL linchan DOT shrchan { Forall (Linear,chan2tyvar $2,chan2svar $4) }
  | FORALL linchan DOT ambig { Forall (Linear,chan2tyvar $2,ambigstype $4) }
  | FORALL linchan DOT addtail { Forall (Linear,chan2tyvar $2,$4 Linear ) }
  | FORALL shrchan DOT error { errr $3 "Expected a session type after '.' here." }
  | FORALL shrchan DOT sessiontype { Forall (Linear,chan2tyvar $2,$4) }
  | FORALL shrchan DOT linchan { Forall (Linear,chan2tyvar $2,chan2svar $4) }
  | FORALL shrchan DOT shrchan { Forall (Linear,chan2tyvar $2,chan2svar $4) }
  | FORALL shrchan DOT ambig { Forall (Linear,chan2tyvar $2,ambigstype $4) }
  | FORALL shrchan DOT addtail { Forall (Linear,chan2tyvar $2,$4 Linear ) }
  | EXISTS linchan DOT error { errr $3 "Expected a session type after '.' here." }
  | EXISTS linchan DOT sessiontype { Exists (Linear,chan2tyvar $2,$4) }
  | EXISTS linchan DOT linchan { Exists (Linear,chan2tyvar $2,chan2svar $4) }
  | EXISTS linchan DOT shrchan { Exists (Linear,chan2tyvar $2,chan2svar $4) }
  | EXISTS linchan DOT ambig { Exists (Linear,chan2tyvar $2,ambigstype $4) }
  | EXISTS linchan DOT addtail { Exists (Linear,chan2tyvar $2,$4 Linear) }
  | EXISTS shrchan DOT error { errr $3 "Expected a session type after '.' here." }
  | EXISTS shrchan DOT sessiontype { Exists (Linear,chan2tyvar $2,$4) }
  | EXISTS shrchan DOT linchan { Exists (Linear,chan2tyvar $2,chan2svar $4) }
  | EXISTS shrchan DOT shrchan { Exists (Linear,chan2tyvar $2,chan2svar $4) }
  | EXISTS shrchan DOT ambig { Exists (Linear,chan2tyvar $2,ambigstype $4) }
  | EXISTS shrchan DOT addtail { Exists (Linear,chan2tyvar $2,$4 Linear) }

wedge_types:
  | error WEDGE { errr $2 "Expected data-level type before '/\\' here." }
  | ambig WEDGE error { errr $2 "Expected session type after '/\\' here." }
  | ambig WEDGE sessiontype { Puretypes.OutD (Linear,ambigmtype $1,$3) }
  | ambig WEDGE linchan { Puretypes.OutD (Linear,ambigmtype $1,chan2svar $3) }
  | ambig WEDGE shrchan { Puretypes.OutD (Linear,ambigmtype $1,chan2svar $3) }
  | ambig WEDGE ambig { Puretypes.OutD (Linear,ambigmtype $1,ambigstype $3) }
  | ambig_brace WEDGE error { errr $2 "Expected session type after '/\\' here." }
  | ambig_brace WEDGE sessiontype { Puretypes.OutD (Linear,abrace2mtype $1,$3) }
  | ambig_brace WEDGE linchan { Puretypes.OutD (Linear,abrace2mtype $1,chan2svar $3) }
  | ambig_brace WEDGE shrchan { Puretypes.OutD (Linear,abrace2mtype $1,chan2svar $3) }
  | ambig_brace WEDGE ambig { Puretypes.OutD (Linear,abrace2mtype $1,ambigstype $3) }

shoe_types:
  | error SHOE { errr $2 "Expected data-level type before '=>' here." }
  | ambig SHOE error { errr $2 "Expected session type after '=>' here." }
  | ambig SHOE sessiontype { Puretypes.InD (Linear,ambigmtype $1,$3) }
  | ambig SHOE linchan { Puretypes.InD (Linear,ambigmtype $1,chan2svar $3) }
  | ambig SHOE shrchan { Puretypes.InD (Linear,ambigmtype $1,chan2svar $3) }
  | ambig SHOE ambig { Puretypes.InD (Linear,ambigmtype $1,ambigstype $3) }
  | ambig_brace SHOE error { errr $2 "Expected session type after '=>' here." }
  | ambig_brace SHOE sessiontype { Puretypes.InD (Linear,abrace2mtype $1,$3) }
  | ambig_brace SHOE linchan { Puretypes.InD (Linear,abrace2mtype $1,chan2svar $3) }
  | ambig_brace SHOE shrchan { Puretypes.InD (Linear,abrace2mtype $1,chan2svar $3) }
  | ambig_brace SHOE ambig { Puretypes.InD (Linear,abrace2mtype $1,ambigstype $3) }

addtail:
  | timestail { $1 }
  | lolitail  { $1 }

timestail:
  |  error TIMES { errr $2 "Expected session type before *" }
  |  stype_atom TIMES sessiontype { fun m -> Puretypes.OutC (m,$1,$3) }
  |  stype_atom TIMES ambig { fun m ->  Puretypes.OutC (m,$1,ambigstype $3) }
  |  stype_atom TIMES addtail { fun m ->  Puretypes.OutC (m,$1,$3 Linear) }
  |  stype_atom TIMES linchan { fun m ->  Puretypes.OutC (m,$1,chan2svar $3) }
  |  stype_atom TIMES shrchan { fun m ->  Puretypes.OutC (m,$1,chan2svar $3) }
  |  linchan TIMES sessiontype { fun m -> Puretypes.OutC (m,chan2svar $1,$3) }
  |  linchan TIMES ambig { fun m ->  Puretypes.OutC (m,chan2svar $1,ambigstype $3) }
  |  linchan TIMES addtail { fun m ->  Puretypes.OutC (m,chan2svar $1,$3 Linear) }
  |  linchan TIMES linchan { fun m ->  Puretypes.OutC (m,chan2svar $1,chan2svar $3) }
  |  linchan TIMES shrchan { fun m ->  Puretypes.OutC (m,chan2svar $1,chan2svar $3) }
  |  shrchan TIMES sessiontype { fun m -> Puretypes.OutC (m,chan2svar $1,$3) }
  |  shrchan TIMES ambig { fun m ->  Puretypes.OutC (m,chan2svar $1,ambigstype $3) }
  |  shrchan TIMES addtail { fun m ->  Puretypes.OutC (m,chan2svar $1,$3 Linear) }
  |  shrchan TIMES linchan { fun m ->  Puretypes.OutC (m,chan2svar $1,chan2svar $3) }
  |  shrchan TIMES shrchan { fun m ->  Puretypes.OutC (m,chan2svar $1,chan2svar $3) }
  |  ambig_notimesarr TIMES sessiontype { fun m -> Puretypes.OutC (m,ambigstype $1,$3) }
  |  ambig_notimesarr TIMES addtail { fun m ->  Puretypes.OutC (m,ambigstype $1,$3 Linear) }
  |  ambig_notimesarr TIMES linchan { fun m ->  Puretypes.OutC (m,ambigstype $1,chan2svar $3) }
  |  ambig_notimesarr TIMES shrchan { fun m ->  Puretypes.OutC (m,ambigstype $1,chan2svar $3) }

lolitail: 
  |  error LOLI { errr $2 "Expected session type before -o" }
  |  stype_atom LOLI sessiontype { fun m -> Puretypes.InC (m,$1,$3) }
  |  stype_atom LOLI ambig { fun m ->  Puretypes.InC (m,$1,ambigstype $3) }
  |  stype_atom LOLI addtail { fun m ->  Puretypes.InC (m,$1,$3 Linear) }
  |  stype_atom LOLI linchan { fun m ->  Puretypes.InC (m,$1,chan2svar $3) }
  |  stype_atom LOLI shrchan { fun m ->  Puretypes.InC (m,$1,chan2svar $3) }
  |  linchan LOLI sessiontype { fun m -> Puretypes.InC (m,chan2svar $1,$3) }
  |  linchan LOLI ambig { fun m ->  Puretypes.InC (m,chan2svar $1,ambigstype $3) }
  |  linchan LOLI addtail { fun m ->  Puretypes.InC (m,chan2svar $1,$3 Linear) }
  |  linchan LOLI linchan { fun m ->  Puretypes.InC (m,chan2svar $1,chan2svar $3) }
  |  linchan LOLI shrchan { fun m ->  Puretypes.InC (m,chan2svar $1,chan2svar $3) }
  |  shrchan LOLI sessiontype { fun m -> Puretypes.InC (m,chan2svar $1,$3) }
  |  shrchan LOLI ambig { fun m ->  Puretypes.InC (m,chan2svar $1,ambigstype $3) }
  |  shrchan LOLI addtail { fun m ->  Puretypes.InC (m,chan2svar $1,$3 Linear) }
  |  shrchan LOLI linchan { fun m ->  Puretypes.InC (m,chan2svar $1,chan2svar $3) }
  |  shrchan LOLI shrchan { fun m ->  Puretypes.InC (m,chan2svar $1,chan2svar $3) }
  |  ambig_notimesarr LOLI sessiontype { fun m -> Puretypes.InC (m,ambigstype $1,$3) }
  |  ambig_notimesarr LOLI ambig { fun m -> Puretypes.InC (m,ambigstype $1,ambigstype $3) }
  |  ambig_notimesarr LOLI addtail { fun m ->  Puretypes.InC (Linear,ambigstype $1,$3 Linear) }
  |  ambig_notimesarr LOLI linchan { fun m ->  Puretypes.InC (Linear,ambigstype $1,chan2svar $3) }
  |  ambig_notimesarr LOLI shrchan { fun m ->  Puretypes.InC (Linear,ambigstype $1,chan2svar $3) }

stype_atom:
  | LPAREN sessiontype RPAREN { Parens $2 }
  | LPAREN linchan RPAREN { Parens (chan2svar $2) }
  | LPAREN shrchan RPAREN { Parens (chan2svar $2) }
  | LPAREN lolitail RPAREN { Parens ($2 Linear) }
  | LPAREN timestail RPAREN { Parens ($2 Linear) }
  | LPAREN error RPAREN { errr $1 "Expected a session type here" }
  | OPLUS choices RBRACE { Intern (Linear,$2) }
  | OPLUS error RBRACE   { errr $1 "Expected label to session type mapping here. E.g., +{foo:1; bar:1}" }
  | AMPR choices RBRACE { Extern (Linear,$2) }
  | AMPR error RBRACE   { errr $1 "Expected label to session type mapping here. E.g., +{foo:1; bar:1}" }

choices:
  | /* empty */ { LM.empty }
  | choice { let (l,s) = $1 in LM.singleton l s }
  | choice SEMI error   { errr $2 "Expected the rest of a session type mapping here. E.g., bar:1}" }
  | choice SEMI choices { let (l,s) = $1 in LM.add $3 l s }

choice:
  | error COLON { errr $2 "Expected branch label (lower case identifier) before ':' here." }
  | FUNNAME COLON error { errr $2 "Expected session type after ':' here." }
  | FUNNAME COLON sessiontype { ($1,$3) }
  | FUNNAME COLON linchan { ($1,chan2svar $3) }
  | FUNNAME COLON shrchan { ($1,chan2svar $3) }
  | FUNNAME COLON ambig { ($1,ambigstype $3) }
  | FUNNAME COLON timestail { ($1,$3 Linear) }
  | FUNNAME COLON lolitail { ($1,$3 Linear) }
