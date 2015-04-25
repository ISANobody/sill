open Base
open Core.Std
open Syntax.Core
open Vars
open Value
open Connection

let topenv : value SM.t ref = ref SM.empty

(* Since we want some ability to make printing backend dependent, we need a real usage of
   modules here *)
module type ExpEvaluator =
sig
  val eval_exp : exp -> memory -> value
end

module MkExpEvaluator = functor (I:Eval_abstract.Impl) -> 
struct 

(* Helper functions to fillout unneeded metadata *)
let nullvar (s:string) : exp = Var (nullinfo,(nullloc,s))
let satfun (n:int) (c:string) =
  let rec go n' e =
    if n' = 0
    then e
    else Fun (nullinfo,(nullloc,"_"^string_of_int n'),go (n'-1) e)
  in go n (Sat (nullinfo,c,List.init n (fun i -> nullvar ("_"^string_of_int (n-i)))))
                                    
let binfun (b:binop) : value = 
Closure("a1",Fun(nullinfo,(nullloc,"a2"),Bin(nullinfo,b,nullvar "a1",nullvar "a2")),SM.empty)
let monfun (m:monop) : value = Closure("a",Mon(nullinfo,m,nullvar "a"),SM.empty)

let conArities = ref (SM.empty : int SM.t)

let const_to_val c = 
  match c with
  | Int i    -> Intval i
  | Float f  -> Floatval f
  | String s -> Stringval s

let monApply op v =
  match op, v with
  | Print, Intval i       -> (I.print (string_of_int i); ADT("()",[]))
  | Sleep, Intval i       -> (Thread.delay (Float.of_int i); ADT("()",[]))
  | Sleep,_ -> failwith "BUG eval_exp.ml: Print got non-Int"
  | Print,_ -> failwith "BUG eval_exp.ml: Print got non-Int"
  | PrintStr, Stringval s -> (I.print s; ADT("()",[]))
  | PrintStr, _ -> failwith "eval_exp.ml: PrintStr got non-String"
  | IToS, Intval i -> Stringval (string_of_int i)
  | IToS, _ -> failwith "eval_exp.ml: IToS got non-Int"
  | SexpToS, v -> Stringval (Sexp.to_string (sexp_of_value v))
  | Neg, Intval i         -> Intval(-i)
  | Neg, _ -> failwith "eval_exp.ml: Neg got non-Int"
  | Assert,ADT("True",[])      ->  ADT("()",[])
  | Assert,ADT("False",[])      ->  I.abort "ASSERT failure"
  | Assert,_ -> failwith "eval_exp.ml: Assert got non-Bool"
  | Flush,ADT("()",[]) -> flush_all (); ADT("()",[])
  | Flush,_ -> I.abort "eval_exp.ml: Flush got non-()"

let binApply (binop:binop) ((v1,v2):value*value) : value =
  match binop, v1, v2 with
    Concat, Value.Stringval x, Value.Stringval y -> Value.Stringval (x ^ y)
  | Eq,_,_  -> if (v1 = v2) then ADT("True",[]) else ADT("False",[])
  | Syntax.Core.Less,_,_  -> if (v1 < v2) then ADT("True",[]) else ADT("False",[])
  | _, Intval x, Intval y -> Intval(
      match binop with
        Add -> x + y
      | Sub -> x - y
      | Mul -> x * y
      | Div -> x / y
      | _ -> failwith "binApply: bad input"
    )
  | _, Floatval x, Floatval y -> Floatval(
      match binop with
        FAdd -> x +. y
      | FSub -> x -. y
      | FMul -> x *. y
      | FDiv -> if y = 0.0 then raise Division_by_zero else x /. y
      | Exp -> x ** y
      | _ -> failwith "binApply: bad input"
    )
  | _ -> failwith ("binApply: bad input: "^string_of_binop binop
                   ^"("^string_of_value v1^", "^string_of_value v2^")")

let rec eval_exp (exp:exp) (m:memory) : value = 
  if !live_trace_flag then print_endline (loc2str (locE exp));
  match exp with 
    Con (_,t) -> const_to_val t
  | Var (_,x)   ->
    (match SM.find m (snd x) with
    | Some (Recvar(f,e,m')) -> eval_exp e (SM.add m' (snd x) (Recvar(f,e,m')))
    | Some v -> v
    | None ->
      (match SM.find !topenv (snd x) with
      | Some (Recvar(f,e,m')) -> eval_exp e (SM.add m' (snd x) (Recvar(f,e,m')))
      | Some v -> v
      | None -> 
        (match SM.find !Types.Dest.conArities (snd x) with
        | Some n -> eval_exp (satfun n (snd x)) m
        | None -> 
          (match snd x with
          | "assert"  -> monfun Assert
          | "print"   -> monfun Print
          | "sleep"   -> monfun Sleep
          | "flush"   -> monfun Flush
          | "print_str" -> monfun PrintStr
          | "i2s" -> monfun IToS
          | "sexp2s" -> monfun SexpToS
          | _ -> failwith ("BUG eval_exp: var not found "^string_of_fvar x^" at "
                          ^loc2string (locE exp) 
                          ^" this should have been caught by typechecking")))))
  | Bin(_,binop, e1, e2) -> binApply binop (eval_exp e1 m, eval_exp e2 m) 
  | Mon(_,monop, e1) -> monApply monop (eval_exp e1 m)
  | App(_,e1, e2) -> 
    (match eval_exp e1 m, eval_exp e2 m with
    | Closure (x,e',m'), v' -> eval_exp e' (SM.add m' x v')
    | _ -> failwith "eval_exp: Can't apply non closure")
  | Let(_,_,f, e1, e2) -> let v = eval_exp e1 (SM.add m (snd f) (Recvar(snd f,e1,m)))
                         in eval_exp e2 (SM.add m (snd f) v)
  | Fun(_,x,e) -> Closure (snd x,e,m)
  | Sat(_,x,args) -> ADT(x,List.map args (fun e -> eval_exp e m))
  | Cas(_,e,pats) -> (
    (match eval_exp e m with
    | ADT(con,vs) ->
                   let (ps,e') = match SM.find pats con with
                                 | Some (x,y) -> (x,y)
                                 | None -> I.abort "couldn't find something BUG"
                   in eval_exp e' (List.fold2_exn ps vs ~init:m
                                    ~f:(fun mx p v -> SM.add mx (snd p) v))
    | _ -> failwith "eval_exp: bad arguments for Case"))
  | Monad (_,outc,p,args,_) -> MonV (outc,args,p,m)
  | Cast (_,e,t) -> (match eval_exp e m with
                  | Boxed (t',v) -> Unify.matchM (puretoptrM t) (puretoptrM t'); v
                  | v -> v)
  | Box (_,e,t) -> failwith "eval Box"
  | PolyApp (i,x,_) -> eval_exp (Var (i,x)) m

end
