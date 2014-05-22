type label = string;
datatype lterm = Number of (IntInf.int)
                        |Label of label
                        |App of lterm*lterm
                        |Abs of label*lterm
                        |Let of ((label*lterm) list) * lterm;
datatype TTerm = VAR of label
                | ARR of TTerm * TTerm
                | LIST of TTerm
                | INT;
type name = char list;
datatype term = Fun of name * term list | Var of name;
type substitution = (name * term ) list; (* triangular form !!! *)
signature UNIFIER = sig
  val unify: term -> term -> substitution option
  val lunify : (term list * term list) option -> substitution option
end;

structure Unifier:UNIFIER = struct
    fun contains var [] = false
    |   contains var ((Var v)::rest) = if (v=var) then true else contains var rest
    |   contains var ((Fun (name,tl))::rest) = if contains var tl then true else contains var rest;

    fun substitute var term [] = []
    |   substitute var term ((Var v)::rest) = (if v=var then term else (Var v))::(substitute var term rest)
    |   substitute var term ((Fun (name,tl))::rest) = (Fun (name,substitute var term tl))::(substitute var term rest);

    fun substituteall [] l = l
    |   substituteall ((name,term)::rest) l = substituteall rest (substitute name term l);

    fun unify (Var t1) (Var t2) : substitution option = if t1=t2 then SOME [] else SOME [(t1,Var t2)]
    |   unify (Var v1) (Fun (f2,tl)) = if (contains v1 tl) then NONE else SOME [(v1,Fun (f2,tl))]
    |   unify (Fun (f1,tl)) (Var v2) = if (contains v2 tl) then NONE else SOME [(v2,Fun (f1,tl))]
    |   unify (Fun (f1,tl1)) (Fun (f2, tl2)) = if (f1=f2) andalso ((length tl1)=(length tl2)) then lunify (SOME (tl1,tl2)) else NONE
    and lunify NONE = NONE
    |   lunify (SOME([],[])) = SOME []
    |   lunify (SOME(a::b,[])) = NONE
    |   lunify (SOME([],a::b)) = NONE
    |   lunify (SOME(vl::restl,vr::restr)) = let
            val vunified = unify vl vr;
            in case vunified
                of NONE => NONE
                |  SOME (v) => let
                    val restunified = lunify (SOME(substituteall v restl,substituteall v restr))
                    in case restunified
                        of NONE => NONE
                        |  SOME(r) => SOME(v@r) end end;
end;

Control.Print.printDepth := 100;
Control.Print.printLength  := 200;