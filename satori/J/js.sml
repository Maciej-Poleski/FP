local

fun contains var [] = false
|   contains var ((Var v)::rest) = if (v=var) then true else contains v rest
|   contains var ((Fun (name,tl))::rest) = if contains var tl then true else contains var rest;

fun substitute_one name term (Var v) = if v=name then term else (Var v)
|   substitute_one name term (Fun (n,tl)) = Fun (n, substitute name term tl)
and substitute var term [] = []
|   substitute var term (t::rest) = (substitute_one var term t)::(substitute var term rest);

fun substituteall [] l = l
|   substituteall ((name,term)::rest) l = substituteall rest (substitute name term l); 

fun add_to_substitution (name:name) (term:term) ([]:substitution) : substitution = [(name,term)]
|   add_to_substitution name term ((n,t)::rest) = (n,(substitute_one name term t))::(add_to_substitution name term rest);

fun unify_impl (Var t1) (Var t2) result : substitution option = if t1=t2 then SOME result else SOME (add_to_substitution t1 (Var t2) result)
|   unify_impl (Var v1) (Fun (f2,tl)) result = if (contains v1 tl) orelse (v1=f2) then NONE else SOME (add_to_substitution v1 (Fun (f2,tl)) result)
|   unify_impl (Fun (f1,tl)) (Var v2) result = if (contains v2 tl) orelse (v2=f1) then NONE else SOME (add_to_substitution v2 (Fun (f1,tl)) result)
|   unify_impl (Fun (f1,tl1)) (Fun (f2, tl2)) result = if (f1=f2) andalso ((length tl1)=(length tl2)) then lunify_impl (SOME (tl1,tl2)) result else NONE
and lunify_impl NONE result = NONE
|   lunify_impl (SOME([],[])) result = SOME result
|   lunify_impl (SOME(a::b,[])) result = NONE
|   lunify_impl (SOME([],a::b)) result = NONE
|   lunify_impl (SOME(vl::restl,vr::restr)) result = let
        val vunified = unify_impl vl vr result;
        in case vunified
            of NONE => NONE
            |  SOME (v) => let
                val restunified = lunify_impl (SOME(substituteall v restl,substituteall v restr)) v
                in case restunified
                    of NONE => NONE
                    |  SOME(r) => SOME(r) end end;

in
    fun unify t1 t2 = unify_impl t1 t2 [];
    fun lunify a = lunify_impl a [];
end;