fun rl ()= use "f3.sml";

val inc= fn n => n+1;
fun add x y = x+y;
fun mult x y = x*y;


fun twice f x = f(f(x));	(* nawiasy dookola x sa zbyteczne, ale tak wyglada bardziej znajomo *)

fun 	fsum f 1= f(1)
	|fsum f n= f(n)+ fsum f (n-1);

(* używając fsum napisz termy obliczające:
	\n -> liczba liczb względnie pierwszych z n, mniejszych od n
	\n -> sumę i^i po wszystkich i < n
	\n -> największa liczba m taka, że 7^m dzieli n!
*)

fun bToi b= case b of
		true => 1
		|false=> 0;
		
fun gcd a 0 = a
| gcd a b = gcd b (a mod b);


fun phi n = fsum (fn a=> bToi ((gcd a n) = 1)) n;

fun sum n = fsum (fn i => let fun mmm a 0 = 1 | mmm a n = a*(mmm a (n-1)) in mmm i i end) (n-1);

fun maxm n = fsum (let fun count i = if (i mod 7 = 0) then 1+count (i div 7) else 0 in count end) n;

fun cK x y = x;	(* kombinator K (przypomnienie) *)
fun cS a b c = (a c) (b c);	(* kombinator S *)
(*
sprobuj przewidzieć wyniki 
	cS add (add 7) 2
	cS add (add 7) 3
	cS add (add 8) 2
	cS mult (add 8) 2
	cS cK cK 42
	cS cK cK 43
*)


(*
Przeanalizuj poniższy kod. Jaki będzie wynik wywołania "fixp foo 7" ?
*)

fun fixp f x = f (fixp f) x;

fun foo f n= if n=0 then 0 else n+ (f (n-1));

(*
napisz term który przekształca liczbę na numeral, oraz drugi który przekształca numeral na liczbę. Zdefiniuj następujące operacje na numeralach  (bez używania operacji na liczbach) inc, add, mult, pow, dec (spróbuj zdefiniować dec tak jak w nietypowanym rachunku lambda), predykat parzystości.
*)

fun gen 0 s z = z
| gen n s z = s(gen (n-1) s z);

fun toInt n = n (fn a=> (a+1)) 0;

fun inc n s z = s(n s z);

fun add a b s z=a s (b s z);

fun mult a b = a (add b) (gen 0);

fun pow a b = b (mult a) (gen 1);

fun even n = n not true;

fun dec n =;