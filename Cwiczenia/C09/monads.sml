infix  3 \>     fun f \> y = f y 

datatype expression = 
		Var of int | 
		Const of int | 
		Plus of  expression*expression | 
		Mult of  expression*expression


local
	fun paren str = "("^str^")"
in
fun exprToString (Var x) = "v"^(Int.toString x)|
	exprToString (Const x) = Int.toString x |
	exprToString (Plus (e1,e2))= paren \> (exprToString e1)^"+"^(exprToString e2) |
	exprToString (Mult (e1,e2))= paren \> (exprToString e1)^"*"^(exprToString e2) 
end

val e1= Plus (Plus (Mult (Const 31, Var 0),Const 13),Mult (Var 0, Var 1) )
val str1= "31*v0+13+v0*v1"

signature Monad=
sig
	type 'a M

	val unit: 'a->'a M
    val bind: 'a M->('a->'b M)-> 'b M
    val seq: 'a M-> 'b M -> 'b M
end

signature MonadPlus= sig
	include Monad
	val zero: 'a M
	val plus: 'a M -> 'a M -> 'a M
end

type cstr = Char.char Stream.stream
type 'a parser =  cstr -> (('a*cstr) Stream.stream)

fun parse p cstr= ...

structure MParser:MonadPlus where type 'a M = 'a parser= struct
	type 'a M = 'a parser

	fun unit x = ...
	fun bind p1 f =...
	fun seq a b= ...

	val zero = ...
	fun plus p1 p2 = ...
end

(*Parser akceptujący znaki spełniające predykat pred *)
fun psat pred = ...

(*Parser akceptujący znak c *)
fun pchar c = ...

infix 1 >>= 
fun op>>= (a,b) = MParser.bind a b

infix 1 >>
fun op>> (a,b) = MParser.seq a b

infix 1 ++ 
fun op++ (a,b) = MParser.plus a b

(* plus s obcięciem *)
fun plusT p1 p2 = ...

infix 1 +++ 
fun op+++ (a,b) = plusT a b


(* parser akceptujący ustalony string
fun pstring str= 

(* parser akceptujący ciąg elementów parsowanych przez p *)
fun pmany p = ...
and pmany1 p= ... (* niepusty ciąg j.w. *)

(* parser akceptujący ciąg elementów parsowanych przez p oddzielonych separatorami akeptowanymi przez sep *)
fun psepby p sep = 
and psepby1 p sep = ... (* niepusty ciąg j.w. *)

(* parser liczby całkowitej dodatniej *)
val pint = ...

(* parsery dla expression Const i Var *)
val pconst = pint >>= (fn n => MParser.unit (Const n))
val pvar = pchar #"v" >> pint >>= (fn n => MParser.unit (Var n))

(* pomocnicze parsery dla Plus i Mult *)
val pplus = pchar #"+"
val pmult = pchar #"*"

(* parser dla expressions *)
fun pterm  cstr= ...
and 
	pparen cstr= ...
and 
	psum cstr = ...
and pmult cstr= ...

