fun rl ()= use "f2.sml";

fun om n = om (n+1);

fun squareSum n= if (n<1) then 0 else (n*n + squareSum(n-1));


fun fibb1 n= case n of	
		  0	=> 1
		| 1	=> 1
		| m	=> (fibb1 (m-1)) + (fibb1 (m-2));

(* jeszcze jeden przykład, żeby było widać, że case nie musi dotyczyć jedynie wartości argumentów *)
fun par n = case (n mod 2) of
		0 => true
		|1 => false;

(* nic ciekawego ale może się przydać *)
(* fun bToi b= case b of
		True => 1
		|False=> 0;
*)
(* jaki błąd jest w powyższej definicji? *)

(*fun fibb2 n = case (Int.compare (n,0)) of 
		 GREATER => if (n=1) then 1 else (fibb2(n-1) + fibb2(n-2))
		| EQUAL  => 1
		| LESS	 => (fibb2 (n+2)) - (fibb2 (n+1));
*)

fun fibb3  0 = 1
	|fibb3  1 = 1
	|fibb3  n = (fibb3 (n-1)) + (fibb3 (n-2));

(* odkomentuj tą funkcję żeby zobaczyć jak nie działa *)
(*
fun 	fibb4  n = (fibb4 (n-1)) + (fibb4 (n-2)) 
	|fibb4  0 = 1
	|fibb4  1 = 1;
*)


(* {- dlaczego poniższa funkcja nie kończy działania dla argumentu 4 (na przykład)? popraw ją -}*)
fun 	fac 1 	= 1
	|fac n	= n * (fac (n-1));

(* napisz predykat pierwszości (jak najbardziej naiwnie) *)

fun isPrime n = (let fun ch i =(if (i<n) then (if ((n mod i)=0) then false else ch (i+1)) else true) in fun 2 end);

(* napisz funkcję gcd obliczającą największy wspólny dzielnik *)
