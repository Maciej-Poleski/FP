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

(*local
    fun skip s n = if n>0 then skip (stl s) (n-1) else s;
    fun make_stream_stream i s n = smemo (fn ss => let val stream = skip s i in (stream,make_stream_stream n stream n) end);
    fun make_grid s i n = if i < n then let
        val current_stream_stream = smap (fn x => stl(x)) s;
    in (smap (fn x => shd(x)) current_stream_stream) :: (make_grid current_stream_stream (i+1) n) end else [] ;
in
    fun ssplitn n s = let
        val stream_stream = make_stream_stream 0 s n;
    in (smap (fn x => shd(x)) stream_stream)::(make_grid stream_stream 1 n) end;
end; *)

local
    fun get_nth i s = if i>0 then get_nth (i-1) (stl s) else s;
    fun make_head c n = smemo (fn _ => (let
        val current = c ();
        in (current, make_head (fn () => get_nth n current) n) end));
    fun make_tail_tail i n sl = if i<n then let
        val current = sl ();
        val current_stream = let fun make c = smemo (fn _ => (shd(shd(c)),make (stl c))); in make current end;
        val next_lazy = (fn () => let fun make s = smemo (fn _ => (stl(shd(s)),make (stl s))); in make current end);
    in current_stream::(make_tail_tail (i+1) n next_lazy) end else [];
    fun make_tail i n sl = let val ss = (make_head sl n) in make_tail_tail i n (fn () => ss) end;
in
    fun ssplitn n s = make_tail 0 n (fn () => s);
end;

local
    fun impl [] sb = smap (fn x => stl(x)) sb
    |   impl (a::b) sb = smemo (fn _ => (a, impl b sb));
in
    fun sinterleave [a] = a
    |   sinterleave (a::b) = smap (fn x => shd(x)) (smemo (fn sb => (a, impl b sb)));
end;
