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
