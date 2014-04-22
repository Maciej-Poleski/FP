local
        val cache = Array.array(2000,NONE)
        fun lookup n = if n<2 then (SOME (1:IntInf.int)) else Array.sub (cache,n)
        fun store n f= (Array.update (cache, n,SOME f); f)
        fun sum Mf n i = (Mf i)*(Mf (n-i)) + (if i>0 then sum Mf n (i-1) else 0:IntInf.int);
in 
        fun M n = (case lookup n of 
                        SOME x => x|
                        NONE   => store n (sum M (n-1) (n-2))
                )
end

signature SUSP =sig
        type 'a susp
        val force : 'a susp -> 'a
        val delay : (unit -> 'a) -> 'a susp
end

structure Susp:>SUSP= struct
        type 'a susp = unit -> 'a ;
        fun force f = f ();
        fun delay f = f;
end

fun YS f = f (Susp.delay (fn () => YS f));

local
    fun impl sf r [] = r
    |   impl sf r [a] = Susp.force sf (a::r) []
    |   impl sf r (a::at) = Susp.force sf (a::r) at;
in
    fun rev1 l = (YS impl) [] l;
end;

datatype 'a stream = Stream of ('a * 'a stream) Susp.susp;

fun seval (Stream sc) = Susp.force sc; 

fun shd s = #1 (seval s);
fun stl s=  #2 (seval s);

fun scons x str = Stream (Susp.delay (fn () => (x, str) ));

fun sconst v = Stream (Susp.delay (fn () => (v, sconst v)));

fun snth 0 s = shd s
|   snth n s = snth (n-1) (stl s);

fun stake 0 s = []
|   stake n s = shd s :: stake (n-1) (stl s);

fun smap f s = Stream (Susp.delay (fn () => (f (shd s), smap f (stl s))));

fun smap1 f s = Stream (Susp.delay (fn () => (f (shd s), stl s)));

fun snat s z = Stream (Susp.delay (fn () => (z, smap s (snat s z))));

fun stab f = smap f (snat (fn n => n+1) 0);

fun szip s t = Stream (Susp.delay (fn () => ((shd s, shd t), szip (stl s) (stl t))));

fun szipwith f s t = smap f (szip s t);

fun sfoldl f start s = Stream (Susp.delay (fn () => (start, sfoldl f (f(start, (shd s))) (stl s))));

fun srev s = stl (sfoldl(fn (a,b) => b::a) [] s);

fun sfilter p s = Stream (Susp.delay (fn () => if p (shd s) then (shd s, sfilter p (stl s)) else seval (sfilter p (stl s))));

fun srepeat t = stab (fn n => List.nth(t, n mod (length t)));

fun spairs s = szip s (stl s);

fun ssplitn n s =
    let
        fun impl i = if i<n then smap (fn (v,_) => v) (sfilter (fn (_,ii) => ((ii mod n) = i)) (szip s (stab (fn n=>n)))) ::(impl (i+1)) else [];
    in impl 0 end;