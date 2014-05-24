infix  3 \>     fun f \> y = f y 

local
  datatype 'a memo_cell = Value of 'a | Computation of unit -> 'a
  exception CellInvalid
  fun make_memo () =
  let
    val cell = ref (Computation (fn _ => raise CellInvalid))
    fun res () =
        case !cell of
          Computation h => (
            let val r = h () in
              cell := Value r;
              r
            end)
        | Value y => y
  in
    (cell, res)
  end
in
  (* fn : ((unit -> 'a) -> 'b * (unit -> 'a)) -> 'b
   * smemo pozwala spamiętywać obliczenia oraz pełni rolę operatora
   * punktu stałego (ze względu na brak rekursji na wartościach
   * w SMLu).
   * Zadaniem 'f' jest skonstruować obliczenie do spamiętania
   * oraz dowolną wartość, którą zwraca memo.
   * Argumentem funkcji 'f' jest to samo obliczenie, które
   * 'f' skonstruuje - ale w opakowanej wersji ze spamiętaniem.
   *)
  fun memo f =
  let
    val (mcell, memoized_computation) = make_memo ()
    val (result, computation) = f memoized_computation
  in
    mcell := Computation computation;
    result
  end
end

structure Stream=struct
	(* Strumień to funkcja zeroargumentowa zwracająca
	 * głowę strumienia oraz ogon. Ze względu na rekursywny
	 * typ, funkcja opakowana jest w konstruktor Stream
	 *)
	datatype 'a stream = Stream of unit -> ('a * 'a stream) option;
	fun seval (Stream f) = f ();
	fun isNil s = not (isSome (seval s));
	fun shd s = #1 \> valOf (seval s);
	fun stl s = #2 \> valOf (seval s);

	(* fn : ('a stream -> 'a * 'a stream) -> 'a stream
	 * smemo tworzy spamiętany strumień. Ten strumień jest
	 * przekazywany do funkcji 'f' jako argument oraz
	 * zwracany przez smemo. Funkcja 'f' konstruuje
	 * początek strumienia - głowę oraz ogon.
	 *)
	fun smemo f = memo (fn the_stream =>
	  let val wrapped_stream = Stream the_stream
		  in (wrapped_stream, fn () => f wrapped_stream)
	  end
	)

	fun snil () = smemo (fn _ => NONE);

	fun fromList [] = snil()
	|   fromList (x::xs) = smemo (fn _ => SOME(x,fromList xs));
	
	fun add a str = smemo (fn _ => SOME(a,str));
	
	fun concatPair str1 str2 = smemo (fn _ => if isNil str1 then seval str2 else SOME(shd str1,concatPair (stl str1) str2));

        fun concat str = smemo (fn _ => if isNil str then NONE else seval (concatPair (shd str) (concat (stl str))));
        
	fun map f str= smemo (fn _ => if isNil str then NONE else SOME(f (shd str),map f (stl str)));
	
	fun toList str = if isNil str then [] else shd str :: toList (stl str);
end
