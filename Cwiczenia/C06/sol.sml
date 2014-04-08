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

