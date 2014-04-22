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

(* Strumień to funkcja zeroargumentowa zwracająca
 * głowę strumienia oraz ogon. Ze względu na rekursywny
 * typ, funkcja opakowana jest w konstruktor Stream
 *)
datatype 'a stream = Stream of unit -> 'a * 'a stream
fun seval (Stream f) = f ();
fun shd s = #1 (seval s);
fun stl s = #2 (seval s);

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

fun sconst x = smemo (fn s => (x,s));

fun snth 0 s = shd s
|   snth n s = snth (n-1) (stl s);

fun stake 0 s = []
|   stake n s = (shd s)::(stake (n-1) (stl s));

fun smap f s = smemo (fn _ => (f(shd(s)),smap f (stl s)));

fun smap1 f s = smemo (fn _ => (f(shd(s)),stl(s)));

fun snat s z = smemo (fn ss => (z,(smap s ss)));

fun stab f = smap f (snat (fn n => n+1) 0);

fun szip s t = smemo (fn _ => ((shd(s),shd(t)),szip (stl s) (stl t)));

fun szipwith f s t = smap f (szip s t);

fun sfoldl f start s = smemo (fn ss => (start, szipwith f ss s));

fun srev s = stl (sfoldl (fn (a,b) => b::a) [] s);

fun sfilter p s = smemo (fn _ => if p (shd s) then (shd s,sfilter p (stl s)) else seval (sfilter p (stl s)));

fun stakewhile p s = if p (shd s) then (shd s)::(stakewhile p (stl s)) else [];

fun srepeat l = smemo (fn ss => let
    fun impl p [] = p
    |   impl p (a::b) = smemo (fn _ => (a, impl p b));
    in seval (impl ss l) end);

fun spairs s = smemo (fn _ => ((shd(s),shd(stl(s))), spairs (stl(stl(s))) ));

fun ssplitn n s = let
    val stream = szip (snat (fn n=>n+1) 0) s;
    fun impl i = if i<n then (smap (fn (_,x) => x) (sfilter (fn (x,_) => x mod n = i) stream))::(impl (i+1)) else [];
    in impl 0 end;

fun sinterleave [a] = a
|   sinterleave (a::b) = smemo (fn _ => (shd a, sinterleave (b @ [(stl a)])));
