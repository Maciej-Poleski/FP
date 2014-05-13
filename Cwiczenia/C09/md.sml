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

