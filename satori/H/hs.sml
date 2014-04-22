fun seval (Stream f) = f ();
fun shd s = #1 (seval s);
fun stl s = #2 (seval s);

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

local
    fun get_nth i s = if i>0 then get_nth (i-1) (stl s) else s;
    fun make_head i n s = smemo (fn _ => (let
        val current = get_nth i s;
        in (shd(current), make_head n n current) end));
    fun make_tail i n s = if i<n then (make_head i n s)::(make_tail (i+1) n s) else [];
in
    fun ssplitn n s = make_tail 0 n s;
end;

fun sinterleave [a] = a
|   sinterleave (a::b) = smemo (fn _ => (shd a, sinterleave (b @ [(stl a)])));

local
    fun make_next [] b c = make_next (rev b) c c
    |   make_next a b c = smemo (fn _ => (hd a,make_next (tl a) b ((hd a)::c)));
in
    val fibonacci = smemo (fn _ => (0,(smemo (fn _ => (1, make_next [0] [1,0] [1,0])))));
end;

local
    fun make1 s = if (shd s) = 1 then smemo (fn _ => (1, make2 (stl s))) else smemo (fn _ => (1,smemo (fn _ => (1, make2 (stl s)))))
    and make2 s = if (shd s) = 1 then smemo (fn _ => (2, make1 (stl s))) else smemo (fn _ => (2,smemo (fn _ => (2, make1 (stl s)))));
in
    val kolakoski = smemo (fn _ => (1,smemo (fn _ => (2,smemo (fn _ => (2, smemo (fn s => (1, smemo (fn _ => (1,make2 s))))))))));
end;

local
    fun gen s = smemo (fn _ => let val i = (shd s) in (i, smemo (fn _ => (1-i, gen (stl s)))) end);
in
    val thuemorse = smemo (fn _ => (0, smemo (fn s => (1, gen s))));
end;
