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

fun parse (p: 'a parser) (cstr: cstr)= p cstr;

structure MParser:MonadPlus where type 'a M = 'a parser= struct
	type 'a M = 'a parser

	fun unit x = fn str => Stream.fromList [(x,str)];
	fun bind p1 f = fn str => Stream.concat (Stream.map (fn (a,str2) => parse (f a) str2) (parse p1 str));
	fun seq a b= fn str => Stream.concat (Stream.map (fn (_,str2) => parse b str2) (parse a str));

	val zero = fn _ => Stream.snil();
	fun plus p1 p2 = fn str => Stream.concatPair (parse p1 str) (parse p2 str);
end

fun pitem str = if Stream.isNil str then Stream.snil() else Stream.fromList [(Stream.shd str,Stream.stl str)];

(*Parser akceptujący znaki spełniające predykat pred *)
fun psat pred = (fn str => if Stream.isNil str orelse not (pred (Stream.shd str)) then Stream.snil() else Stream.fromList [(Stream.shd str,Stream.stl str)]);

(*Parser akceptujący znak c *)
fun pchar c = psat (fn x => x=c);

infix 1 >>= 
fun op>>= (a,b) = MParser.bind a b

infix 1 >>
fun op>> (a,b) = MParser.seq a b

infix 1 ++ 
fun op++ (a,b) = MParser.plus a b

(* plus s obcięciem *)
fun plusT p1 p2 = fn str => let
    val l = parse p1 str;
    in if Stream.isNil l then parse p2 str else l end;

infix 1 +++ 
fun op+++ (a,b) = plusT a b


(* parser akceptujący ustalony string *)
fun pstring str= if str="" then MParser.unit "" else pchar (String.sub(str,0)) >> pstring (String.extract(str,1,NONE)) >> MParser.unit str;

(* parser akceptujący ciąg elementów parsowanych przez p *)
fun pmany p = (pmany1 p) +++ (MParser.unit (Stream.snil ()))
and pmany1 p= (p >>= (fn a => (pmany p) >>= (fn ar => MParser.unit (Stream.add a ar))));

(* parser akceptujący ciąg elementów parsowanych przez p oddzielonych separatorami akeptowanymi przez sep *)
fun psepby p sep = (psepby1 p sep) +++ (MParser.unit (Stream.snil()))
and psepby1 p sep = p >>= (fn a => (pmany (sep >> p)) >>= (fn ar => MParser.unit (Stream.add a ar)));

fun pchainl p ope a = (pchainl1 p ope) +++ (MParser.unit a)
and pchainl1 p ope = p >>= (fn a => (let
    fun rest a = (ope >>= (fn f => p >>= (fn b => rest (f a b)))) +++ (MParser.unit a)
    in rest a end));
    
fun pchainr p ope a = (pchainr1 p ope) +++ (MParser.unit a)
and pchainr1 p ope = p >>= (fn a => (ope >>= (fn f => ((pchainr1 p ope) >>= (fn b => MParser.unit (f a b))))) +++ (MParser.unit a));
    
val pspace = pmany (psat Char.isSpace);

(* Usuwa spacje TYLKO na końcu *)
fun ptoken p = p >>= (fn a => pspace >> (MParser.unit a));

fun psymb (cs:string) = ptoken (pstring cs);

fun apply p = parse (pspace >> p);

(* parser liczby całkowitej dodatniej *)
val pint = (pmany1 (psat Char.isDigit)) >>= (fn str => MParser.unit(valOf(Int.fromString (implode (Stream.toList str)))));

(* parsery dla expression Const i Var *)
val pconst = pint >>= (fn n => MParser.unit (Const n))
val pvar = pchar #"v" >> pint >>= (fn n => MParser.unit (Var n))

(* pomocnicze parsery dla Plus i Mult *)
val pplusa = pchar #"+"
val pmulta = pchar #"*"

val psumop = pplusa >> MParser.unit (fn a => fn b => (Plus(a,b)));
val pmulop = pmulta >> MParser.unit (fn a => fn b => (Mult(a,b)));

(* parser dla expressions *)
fun pterm  cstr= (print "pterm\n"; (pconst ++ pvar ++ pparen) cstr)
and 
	pparen cstr=(print "pparen\n"; (pchar #"(" >> psum >>= (fn a => pchar #")" >> MParser.unit a)) cstr)
and 
	psum cstr = pchainr1 pmult psumop cstr
and pmult cstr= pchainr1 pterm pmulop cstr;

