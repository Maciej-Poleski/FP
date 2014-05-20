structure T = TYPECHECK(Unifier);
(* val context = [("K",ARR(VAR "a",ARR(VAR "b",VAR "a"))),("S",ARR(ARR (VAR "11",ARR (VAR "13",VAR "14")),ARR (ARR (VAR "11",VAR "13"),ARR (VAR "11",VAR "14"))))]; *)

local
                infixr 6 -->
                fun a --> b= ARR (a,b)
in
                val context= [
                        ("PLUS",INT --> INT --> INT),
                        ("CONS", VAR "a" --> (LIST (VAR "a")) --> (LIST (VAR "a"))),
                        ("NIL", LIST (VAR "a")),
                        ("hd",(LIST (VAR "a")) --> VAR "a")
                        ]
end;

let
        fun S a b c = a c (b c)
        fun K a b = a
in S K K end;

val funS=Abs("a",Abs("b",Abs("c",App(App(Label "a", Label "c"),App(Label "b", Label "c")))));
val funK=Abs("a",Abs("b",Label "a"));

val l=Let([("S",funS),("K",funK)],App(App(Label "S",Label "K"),Label "K"));

(*let
    fun isNil l = 0
    fun concat l = IF (isNil l) NIL (let
            val firstL = hd l
            val restL = tl l
            in IF (isNil firstL) (concat restL) ((hd firstL)::(concat ((tl firstL)::(restL)))) end)
in   concat
end
end *)