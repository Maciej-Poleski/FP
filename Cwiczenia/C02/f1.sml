val inc1 = fn n => n+1 ;

fun inc2 n = ((op +) (1,n)) ;

val inc= inc1;

fun par n = (n mod 2) = 0 ; (* uwaga na różne równości i kolejność wiązania *)

fun cK x y = x;	(* kombinator K *)
(*
nie musimy nazywać argumentów, których nie używamy, cK możemy równie dobrze zdefiniować jako 
	fun cK x _ = x;
*)

fun perim r = let 
		val pi= 3.14;
	in 2.0* pi * r end;

fun cArea r= let 
		val pi= 3.14;
		val r2= r*r;
	in pi * r2 end;

fun rl () = use "f1.sml";
