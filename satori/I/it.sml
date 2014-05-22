structure T = TYPECHECK(Unifier);
(* val context = [("K",ARR(VAR "a",ARR(VAR "b",VAR "a"))),("S",ARR(ARR (VAR "11",ARR (VAR "13",VAR "14")),ARR (ARR (VAR "11",VAR "13"),ARR (VAR "11",VAR "14"))))]; *)

local
                infixr 6 -->
                fun a --> b= ARR (a,b)
in
                val context= [
(*                         ("PLUS",INT --> INT --> INT), *)
(*                         ("CONS", VAR "a" --> (LIST (VAR "a")) --> (LIST (VAR "a"))), *)
(*                         ("NIL", LIST (VAR "a")), *)
                        ("hd",(LIST (VAR "a")) --> VAR "a")
(*                         ("IF",INT --> VAR "a" --> VAR "a" --> VAR "a"), *)
(*                         ("tl",LIST (VAR "a") --> LIST (VAR "a")) *)
                        ]
end;

(*let
        fun foldl f z l1 =IF 0 z (foldl f (f z (hd l1)) (tl l1))
        val ones = 1::ones

        fun add x y = x+y
        fun f1 i = 1+ (f2 i)
        fun f2 i = 1+ (f1 i)
in  foldl add   end;*)

val t2=Let([("foldl",Abs("f",Abs("z",Abs("l1",App(App(App(Label "IF",Number 0),Label "z"),App(App(App(Label "foldl",Label "f"),App(App(Label "f",Label "z"),App(Label "hd",Label "l1"))),App(Label "tl",Label "l1"))))))),("ones",App(App(Label "CONS",Number 1),Label "ones")),("add",Abs("x",Abs("y",App(App(Label "PLUS", Label "x"),Label "y")))),("f1",Abs("i",App(App(Label "PLUS", Number 1),App(Label "f2", Label "i")))),("f2",Abs("i",App(App(Label "PLUS", Number 1),App(Label "f1", Label "i"))))],App(Label "foldl", Label "add"));

val t=App(Abs("I",Let([("x",Let([("y",App(Label "I",Number 7))],App(Label "I", Label "x")))],Label "x")),Abs("x",Label "x"));

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
end;*)

val ift1=App(App(App(Label "IF",App(Label "isNil", Label "firstL")),App(Label "concat",Label "restL")),App(App(Label "CONS",App(Label "hd",Label "firstL")),App(Label "concat",App(App(Label "CONS",App(Label "tl",Label "firstL")),Label "restL"))));

val let2=Let([("firstL",App(Label "hd",Label "l")),("restL",App(Label "tl",Label "l"))],ift1);

val concatt=Abs("l",App(App(App(Label "IF",App(Label "isNil",Label "l")),Label "NIL"),let2));

val t3=Let([("isNil",Abs("l",Number 0)),("concat",concatt)],Label "isNil");

let
    fun id x = x;
    fun id2 a = let
        val b = id a;
        val c = hd b;
        in id c end; (* Tutaj tworzona jest instancja zgeneralizowanej c gubiąc ograniczenia nałożone na c w podstawieniu *)
    in id2 end;

val letid2=Let([("b",App(Label "id",Label "a")),("c",App(Label "hd", Label "b"))],App(Label "id",Label "c"));
val t4=Let([("id",Abs("x",Label "x")),("id2",Abs("a",letid2))],Label "id2");
