infix  3 \>     fun f \> y = f y 

local
  datatype 'a memo_cell = Value of 'a | Computation of unit -> 'a
  exception CellInvalid
  fun make_memo () =
  let
    val cell = ref (Computation (fn _ => raise CellInvalid))
    fun res () =
        case !cell of
          Computation h => (
            let val r = h () in
              cell := Value r;
              r
            end)
        | Value y => y
  in
    (cell, res)
  end
in
  (* fn : ((unit -> 'a) -> 'b * (unit -> 'a)) -> 'b
   * smemo pozwala spamiętywać obliczenia oraz pełni rolę operatora
   * punktu stałego (ze względu na brak rekursji na wartościach
   * w SMLu).
   * Zadaniem 'f' jest skonstruować obliczenie do spamiętania
   * oraz dowolną wartość, którą zwraca memo.
   * Argumentem funkcji 'f' jest to samo obliczenie, które
   * 'f' skonstruuje - ale w opakowanej wersji ze spamiętaniem.
   *)
  fun memo f =
  let
    val (mcell, memoized_computation) = make_memo ()
    val (result, computation) = f memoized_computation
  in
    mcell := Computation computation;
    result
  end
end

structure Stream=struct
        (* Strumień to funkcja zeroargumentowa zwracająca
         * głowę strumienia oraz ogon. Ze względu na rekursywny
         * typ, funkcja opakowana jest w konstruktor Stream
         *)
        datatype 'a stream = Stream of unit -> ('a * 'a stream) option;
        fun seval (Stream f) = f ();
        fun isNil s = not (isSome (seval s));
        fun shd s = #1 \> valOf (seval s);
        fun stl s = #2 \> valOf (seval s);

        (* fn : ('a stream -> 'a * 'a stream) -> 'a stream
         * smemo tworzy spamiętany strumień. Ten strumień jest
         * przekazywany do funkcji 'f' jako argument oraz
         * zwracany przez smemo. Funkcja 'f' konstruuje
         * początek strumienia - głowę oraz ogon.
         *)
        fun smemo f = memo (fn the_stream =>
          let val wrapped_stream = Stream the_stream
                  in (wrapped_stream, fn () => f wrapped_stream)
          end
        )

        fun snil () = smemo (fn _ => NONE);

        fun fromList [] = snil()
        |   fromList (x::xs) = smemo (fn _ => SOME(x,fromList xs));
        
        fun add a str = smemo (fn _ => SOME(a,str));
        
        fun concatPair str1 str2 = smemo (fn _ => if isNil str1 then seval str2 else SOME(shd str1,concatPair (stl str1) str2));

        fun concat str = smemo (fn _ => if isNil str then NONE else seval (concatPair (shd str) (concat (stl str))));
        
        fun map f str= smemo (fn _ => if isNil str then NONE else SOME(f (shd str),map f (stl str)));
        
        fun toList str = if isNil str then [] else shd str :: toList (stl str);
end


signature Monad=
sig
        type 'a M

        val unit: 'a->'a M
    val bind: 'a M->('a->'b M)-> 'b M
    val seq: 'a M-> 'b M -> 'b M
end

signature MonadPlus= sig
        include Monad
        val zero: 'a M
        val plus: 'a M -> 'a M -> 'a M
end

type cstr = Char.char Stream.stream
type 'a parser =  cstr -> (('a*cstr) Stream.stream)

fun parse (p: 'a parser) (cstr: cstr)= p cstr;

structure MParser:MonadPlus where type 'a M = 'a parser= struct
        type 'a M = 'a parser

        fun unit x = fn str => Stream.fromList [(x,str)];
        fun bind p1 f = fn str => Stream.concat (Stream.map (fn (a,str2) => parse (f a) str2) (parse p1 str));
        fun seq a b= fn str => Stream.concat (Stream.map (fn (_,str2) => parse b str2) (parse a str));

        val zero = fn _ => Stream.snil();
        fun plus p1 p2 = fn str => Stream.concatPair (parse p1 str) (parse p2 str);
end

fun pitem str = if Stream.isNil str then Stream.snil() else Stream.fromList [(Stream.shd str,Stream.stl str)];

(*Parser akceptujący znaki spełniające predykat pred *)
fun psat pred = (fn str => if Stream.isNil str orelse not (pred (Stream.shd str)) then Stream.snil() else Stream.fromList [(Stream.shd str,Stream.stl str)]);

(*Parser akceptujący znak c *)
fun pchar c = psat (fn x => x=c);

infix 1 >>= 
fun op>>= (a,b) = MParser.bind a b

infix 1 >>
fun op>> (a,b) = MParser.seq a b

infix 1 ++ 
fun op++ (a,b) = MParser.plus a b

(* plus s obcięciem *)
fun plusT p1 p2 = fn str => let
    val l = parse p1 str;
    in if Stream.isNil l then parse p2 str else l end;

infix 1 +++ 
fun op+++ (a,b) = plusT a b


(* parser akceptujący ustalony string *)
fun pstring str= if str="" then MParser.unit "" else pchar (String.sub(str,0)) >> pstring (String.extract(str,1,NONE)) >> MParser.unit str;

(* parser akceptujący ciąg elementów parsowanych przez p *)
fun pmany p = (pmany1 p) +++ (MParser.unit (Stream.snil ()))
and pmany1 p= (p >>= (fn a => (pmany p) >>= (fn ar => MParser.unit (Stream.add a ar))));

(* parser akceptujący ciąg elementów parsowanych przez p oddzielonych separatorami akeptowanymi przez sep *)
fun psepby p sep = (psepby1 p sep) +++ (MParser.unit (Stream.snil()))
and psepby1 p sep = p >>= (fn a => (pmany (sep >> p)) >>= (fn ar => MParser.unit (Stream.add a ar)));

fun pchainl p ope a = (pchainl1 p ope) +++ (MParser.unit a)
and pchainl1 p ope = p >>= (fn a => (let
    fun rest a = (ope >>= (fn f => p >>= (fn b => rest (f a b)))) +++ (MParser.unit a)
    in rest a end));
    
fun pchainr p ope a = (pchainr1 p ope) +++ (MParser.unit a)
and pchainr1 p ope = p >>= (fn a => (ope >>= (fn f => ((pchainr1 p ope) >>= (fn b => MParser.unit (f a b))))) +++ (MParser.unit a));
    
val pspace = pmany (psat Char.isSpace);

(* Usuwa spacje TYLKO na końcu *)
fun ptoken p = p >>= (fn a => pspace >> (MParser.unit a));

fun psymb (cs:string) = ptoken (pstring cs);

fun apply p = parse (pspace >> p);

(* parser liczby całkowitej dodatniej *)
val pint = (pmany1 (psat Char.isDigit)) >>= (fn str => MParser.unit(valOf(Int.fromString (implode (Stream.toList str)))));
val pintinf = (pmany1 (psat Char.isDigit)) >>= (fn str => MParser.unit(valOf(IntInf.fromString (implode (Stream.toList str)))));

val inputStream = let
    fun makeInputStream () = Stream.smemo (fn _ => case TextIO.input1 TextIO.stdIn of NONE => NONE | SOME(c) => SOME(c, makeInputStream() ));
    in makeInputStream () end;


val pnumber = pintinf >>= (fn a => MParser.unit (Number a));

local
    val keywords = ["fn","let","in","end","val","fun"];
    in
    fun is_keyword str = (*false *)List.exists (fn x => str = x) keywords;
end;

val pstringlabel : label MParser.M =(psat Char.isAlpha) >>= (fn a => pmany (psat Char.isAlphaNum) >>= (fn ar => let val r= implode (a::(Stream.toList ar)) in if is_keyword r then MParser.zero else MParser.unit r end));

val plabel : lterm MParser.M = pstringlabel >>= (fn label => MParser.unit (Label(label)));

val pspace_r = pmany1 (psat Char.isSpace);

val pspace_o = pmany (psat Char.isSpace);

val pappop = pspace_o >> MParser.unit (fn a => fn b => App(a,b));

val pcatop = pspace_o >> pstring "::" >> pspace_o >> MParser.unit (fn a => fn b => App(App(Label "CONS",a),b));

val pplusop = pspace_o >> pchar #"+" >> pspace_o >> MParser.unit (fn a => fn b => App(App(Label "PLUS",a),b));

val pletdefinitionop : ((label*lterm) list ->(label*lterm) list ->(label*lterm) list) MParser.M = pspace_o >> MParser.unit (fn a => fn b => a@b);

val pdefinition_fun_args_op : (label list ->label list -> label list) MParser.M = pspace_r >> MParser.unit (fn a => fn b => a@b);

fun build_fun ([]: label list) (term: lterm) : lterm  = term
|   build_fun (a::ar) term = Abs(a,build_fun ar term);

fun pterm cstr  = (pparen ++ pnumber ++ plabel ++ pfn ++ plet) cstr
and pparen cstr = (pchar #"(" >> pspace_o >> papp >>= (fn app => pspace_o >> pchar #")" >> MParser.unit app)) cstr
and papp cstr = (pchainl1 pcat pappop) cstr
and pcat cstr = (pchainr1 pplus pcatop) cstr
and pplus cstr = (pchainl1 pterm pplusop) cstr
and pfn cstr = (pstring "fn" >> pspace_r >> pstringlabel >>= (fn label => pspace_o >> pstring "=>" >> pspace_o >> papp >>= (fn app => MParser.unit (Abs(label,app))))) cstr
and plet cstr = (pstring "let" >> pspace_r >> (pchainr pdefinition pletdefinitionop []) >>= (fn definitions => pspace_r >> pstring "in" >> pspace_r >> papp >>= (fn term => pspace_r >> pstring "end" >> MParser.unit (Let(definitions,term))))) cstr
and pdefinition cstr = ((pdefinition_val ++ pdefinition_fun) >>= (fn definition => MParser.unit ([definition])) ) cstr
and pdefinition_val cstr = (pstring "val" >> pspace_r >> pstringlabel >>= (fn label => pspace_o >> pchar #"=" >> pspace_o >> papp >>= (fn term => MParser.unit (label,term)))) cstr
and pdefinition_fun cstr = (pstring "fun" >> pspace_r >> pstringlabel >>= (fn name => pspace_r >> (pchainr1 (pstringlabel >>= (fn l  => MParser.unit ([l]))) pdefinition_fun_args_op) >>= (fn args => pspace_o >> pchar #"=" >> pspace_o >> papp >>= (fn term => MParser.unit (name, (build_fun args term)))))) cstr;
(* and pdefinition_fun cstr = (MParser.unit ("asdf",Number(1))) cstr; *)

fun parseSml (cstr: cstr) : lterm option= let
    val resultStream = parse papp cstr;
    in case Stream.isNil resultStream of true => NONE | false => SOME(#1 (Stream.shd resultStream)) end;

fun print_term NONE = print "NO PARSE"
|   print_term (SOME t) = print (lterm2str t);

fun parseT (str: string) : lterm = valOf (parseSml (Stream.fromList (explode str)));

print_term (parseSml inputStream);
