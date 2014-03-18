datatype 'a List = Nil | Cons of ('a * ('a List));

fun len Nil = 0
 | len (Cons(_,r))= 1+len(r);

fun addFirst a el = Cons(el,a);
fun addLast Nil el = Cons(el,Nil)
|   addLast (Cons(a,b)) el=Cons(a,addLast b el);

fun cat Nil x = x
|   cat (Cons(a,b)) Nil = Cons(a,b)
|   cat (Cons(a,b)) (Cons(c,d)) = Cons(a,cat b (Cons(c,d)));

fun rev Nil = Nil
|   rev (Cons(a,b)) = addLast (rev b) a;

(*fun lFilter (predicate: 'a -> bool) (list: 'a List) : ('a List) =
  let fun impl Nil = Nil
	| impl (Cons(a,b)) = if predicate a then Cons(a,impl b) else impl b
  in impl list
  end; *)

fun lFilter (predicate: 'a -> bool) (Nil: 'a List) : ('a List) = Nil
|   lFilter (predicate: 'a -> bool) (Cons(a,b): 'a List) : ('a List) = if predicate a then Cons(a,lFilter predicate b) else lFilter predicate b;

fun lMap (f: 'a -> 'b) (Nil: 'a List) : ('b List) = Nil
|   lMap (f: 'a -> 'b) (Cons(a,b): 'a List) : ('b List) = Cons(f a,lMap f b);

fun last (a::nil: 'a list) : 'a = a
|   last (a::b: 'a list) : 'a = last b;

datatype 'elType Pair = Pair of 'elType*'elType;

fun first (Pair(a,b) : 'a Pair) : 'a = a;
fun second (Pair(a,b) : 'a Pair) : 'a = b;

datatype ('elType1,'elType2)  Pair= Pair of 'elType1*'elType2;
fun first (Pair(a,b) : ('a, 'b) Pair) : 'a = a;
fun second (Pair(a,b) : ('a, 'b) Pair) : 'b = b;

fun rev (list: 'a list) =
  let
    fun impl (result,[]) = (result,[])
    |   impl (result,a::b) = impl (a::result,b)
  in
    #1(impl ([],list))
  end;

fun curry acbc = fn a => fn b => acbc (a, b);
fun decurry abc = fn (a,b) => abc a b;

fun zip ([]: 'a list) ([]: 'b list) : ('a*'b) list = []
|   zip (a::ar: 'a list) (b::br: 'b list) : ('a*'b) list = (a,b)::(zip ar br);

fun f a b= map (decurry (fn a => fn b => a+b)) (zip a b);
