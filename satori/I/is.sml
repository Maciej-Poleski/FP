    signature COMPARABLE = sig
            type t;
            val cmp: t*t -> order;
    end;
    signature DICT= sig
        structure Key:COMPARABLE;

        type 'vt dict;

        val empty: 'vt dict;
        val insert: (Key.t * 'vt) * 'vt dict -> 'vt dict;
        val lookup: (Key.t * 'vt dict) -> 'vt option;
    end;
    datatype 'a node = Two of 'a node * 'a * 'a node |
                    Three of 'a node * 'a * 'a node * 'a * 'a node |
                    Empty;

    datatype 'b Propagate= Good of 'b | PropagateUp of 'b;

    signature SPEC = sig
        structure Key:COMPARABLE;
        type 'vT entryT;
        type 'vT resultT;
        
        val extractKey: 'vT entryT -> Key.t;
        val updateE: 'vT entryT node * 'vT entryT -> 'vT entryT node Propagate;
        val lookupE: 'vT entryT option -> 'vT resultT;
    end;
    
    functor TFrame(structure Spec:SPEC)= struct
        type 'vt frame= 'vt Spec.entryT node;
        val empty = Empty;
        fun lookup (key,  Empty) = Spec.lookupE NONE
        |   lookup (key, Two (left, y, right)) = (case Spec.Key.cmp (key, Spec.extractKey y) of LESS => lookup (key, left)
                                                                            |  EQUAL => Spec.lookupE (SOME y)
                                                                            |  GREATER => lookup (key, right))
        |   lookup (key, Three (left, y, center, z, right)) = (case Spec.Key.cmp (key, Spec.extractKey y) of LESS => lookup (key, left)
                                                                                        |  EQUAL => Spec.lookupE (SOME y)
                                                                                        |  GREATER => (case Spec.Key.cmp (key, Spec.extractKey z) of LESS => lookup (key, center)
                                                                                                                                |  EQUAL => Spec.lookupE (SOME z)
                                                                                                                                |  GREATER => lookup (key, right)));
        fun insert (entry,  tree) = case Spec.updateE (tree, entry) of Good (r) => r | PropagateUp (r) => r;
    end;

    datatype 'a result = Single of 'a node (* węzeł *)
    |                    Double of 'a * 'a node * 'a node; (* wartość, lewy, prawy *)

    fun impl cmp (x, (Empty)) = Single (Two (Empty, x, Empty))
    |   impl cmp (x, (Two (Empty, y, Empty))) =
            (case (cmp (x,y)) of LESS => Single(Three(Empty, x, Empty, y, Empty))
                                |  EQUAL => Single(Two(Empty,x,Empty))
                                |  GREATER => Single(Three(Empty, y, Empty, x, Empty)))
    |   impl cmp (x, (Three (Empty, y, Empty, z, Empty))) =
            (case (cmp (x,y)) of LESS => Double(y, Two(Empty, x, Empty), Two(Empty, z, Empty))
                                |  EQUAL => Single(Three(Empty, x, Empty, z, Empty))
                                |  GREATER => (case (cmp (x,z)) of LESS => Double(x, Two(Empty, y, Empty), Two(Empty, z ,Empty))
                                                                |  EQUAL => Single(Three(Empty, y, Empty, x, Empty))
                                                                |  GREATER => Double(z, Two(Empty, y, Empty), Two(Empty, x, Empty))))
    |   impl cmp (x, (Two (left, y, right))) =
            (case (cmp (x,y)) of LESS => (case impl cmp (x, left) of Single (n) => Single (Two (n, y, right))
                                            |                          Double (n, l, r) => Single (Three (l, n, r, y, right)))
                                |  EQUAL => Single(Two(left, x, right))
                                |  GREATER => (case impl cmp (x, right) of Single (n) => Single (Two (left, y, n))
                                                |                           Double (n, l, r) => Single (Three (left, y, l, n, r))))
    |   impl cmp (x, (Three (left, y, center, z, right))) =
            (case (cmp (x,y)) of LESS => (case impl cmp (x, left) of Single (n) => Single (Three (n, y, center, z, right))
                                            |                          Double (n, l, r) => Double (y, Two (l, n, r), Two (center, z, right)))
                                |  EQUAL => Single(Three(left, x, center, z, right))
                                |  GREATER => (case (cmp (x,z)) of LESS => (case impl cmp (x, center) of Single (n) => Single (Three (left, y, n, z, right))
                                                                            |                            Double (n, l, r) => Double (n, Two (left, y, l), Two (r, z, right)))
                                                                |  EQUAL => Single(Three(left, y, center, x, right))
                                                                |  GREATER => (case impl cmp (x, right) of Single (n) => Single (Three (left, y, center, z, n))
                                                                                |                           Double (n, l, r) => Double (z, Two (left, y, center), Two (l, n, r)))));

    functor DSpec (structure KeyS:COMPARABLE):SPEC = struct
        structure Key:COMPARABLE = KeyS;
        type 'vT entryT = KeyS.t * 'vT;
        type 'vT resultT = 'vT option;
        
        fun extractKey (key, _) = key;
        fun updateE (T, x) = 
            case impl (fn ((xk,xv),(yk,yv)) => KeyS.cmp (xk,yk)) (x, T) of Single (n) => Good(n)
            |                       Double (n, left, right) => PropagateUp( Two(left, n, right));
        fun lookupE (NONE) = NONE
        |   lookupE (SOME(key,value)) = SOME(value);
    end;
    
    functor TDict(structure KeyS:COMPARABLE):>DICT where type Key.t=KeyS.t = struct
        structure Spec:SPEC=DSpec(structure KeyS=KeyS);
        structure Frame= TFrame(structure Spec= Spec);

        structure Key:COMPARABLE=KeyS;
        type 'vt dict= 'vt Frame.frame;

        val empty= Frame.empty;
        val insert= Frame.insert;
        val lookup= Frame.lookup;
    end;
    
functor TYPECHECK(U:UNIFIER) = struct
(*     Implementacja     *)
    
    structure LabelCmp: COMPARABLE = struct
        type t = label;
        fun cmp (a,b) = String.compare(a,b);
    end;
    
    structure context_t = TDict(structure KeyS=LabelCmp);

    datatype ttype = VAR_ of label
                    | GENERIC_ of label
                    | ARR_ of ttype * ttype
                    | LIST_ of ttype
                    | INT_;
    
    local
        val instance_count = ref 0;
    
        fun make_new_instance_name l = concat [l,Int.toString (!instance_count)];
        fun impl ((INT_): ttype) : TTerm = INT
        |   impl (VAR_ l) = VAR l
        |   impl (GENERIC_ l) = VAR (make_new_instance_name l)
        |   impl (ARR_ (a,b)) = ARR (impl a, impl b)
        |   impl (LIST_ (a)) = LIST (impl a);
    in
        fun instantiate term = let
            val result = impl term;
            val () = instance_count := (!instance_count) + 1;
        in result end;
    end;

    (* Tworzy nową instancje na podstawie wybranego schematu typu z kontekstu *)
    fun get_label_instance (l:label) (context: ttype context_t.dict) = case context_t.lookup(l,context)
                                                                of NONE => NONE
                                                                |  SOME(t) => SOME (instantiate t);
    
    local
        val count = ref 0;
    in
        fun get_new_type_variable_name () = let
            val result = Int.toString (!count);
            val () = count := (!count) + 1;
        in result end;
    end;
    
    (* Konwertuje TTerm do term na potrzeby unifikacji *)
    fun TTerm_to_term (VAR l) = Var (explode l)
    |   TTerm_to_term (ARR (a,b)) = Fun ((explode "ARR"), map TTerm_to_term [a,b])
    |   TTerm_to_term (LIST (a)) = Fun ((explode "LIST"), [TTerm_to_term a])
    |   TTerm_to_term (INT) = Fun ((explode "INT"),[]);
    
    (* Konwertuje term do TTerm aby powrócić z unifikacji do formatu wyjściowego *)
    fun term_to_TTerm (Var name) = VAR (implode name)
    |   term_to_TTerm (Fun (name, termList)) = case implode name
                                                of "ARR" => ARR (term_to_TTerm (hd termList), term_to_TTerm (hd(tl termList)))
                                                |  "LIST" => LIST (term_to_TTerm (hd termList))
                                                |  "INT" => INT;
    
    fun substitution_to_termLists sub = foldr (fn ((n,t),(l,r)) => ((Var n)::l,t::r)) ([],[]) sub;
    
    fun add_tterm_to_context (name: label) (term: ttype) context = context_t.insert((name,term),context);

    fun impl (Number _) context : (TTerm*substitution) option = SOME(INT,[])
    |   impl (Label label) context = (case get_label_instance label context
                                        of NONE => NONE
                                        |  SOME(t) => SOME((t,[])))
    |   impl (App (a,b)) context = let
            val aResult = impl a context;
            val bResult = impl b context;
        in (case aResult
            of NONE => NONE
            |  SOME(aType, aSubstitution) =>
                (case bResult
                 of NONE => NONE
                 |  SOME(bType, bSubstitution) => let
                        val new_variable = VAR (get_new_type_variable_name ());
                        val (al,ar) = substitution_to_termLists aSubstitution;
                        val (bl,br) = substitution_to_termLists bSubstitution;
                        val newL = TTerm_to_term aType;
                        val newR = TTerm_to_term (ARR (bType,new_variable));
                        val leftTerms = newL :: al @ bl;
                        val rightTerms = newR :: ar @ br;
                        val resultSubstitution = U.lunify (SOME (leftTerms,rightTerms));
                    in (case resultSubstitution of NONE => NONE | SOME(s) => SOME(new_variable,s)) end)) end
    |   impl (Abs (l,t)) context = let
            val new_variable = VAR_ (get_new_type_variable_name ());
            val new_context = add_tterm_to_context l new_variable context;
        in case impl t new_context
            of NONE => NONE
            |  SOME(upperType,subs) => let
                val result_variable = VAR (get_new_type_variable_name ());
                val (upperL,upperR) = substitution_to_termLists subs;
                val newL = TTerm_to_term result_variable;
                val newR = TTerm_to_term (ARR (valOf (get_label_instance l new_context),upperType));
                val leftTerms = newL :: upperL;
                val rightTerms = newR :: upperR;
                val resultSubstitution = U.lunify (SOME (leftTerms,rightTerms));
            in case resultSubstitution of NONE => NONE | SOME(s) => SOME(result_variable,s) end end;
    (*|   impl (Let _) context = NONE;*)
    
    local       (* Generalizuje TTerm do ttype *)
        fun parse_TTerm ((VAR label): TTerm) : ttype = GENERIC_ label
        |   parse_TTerm (ARR (a,b)) = ARR_ (parse_TTerm a, parse_TTerm b)
        |   parse_TTerm (LIST a) = LIST_ (parse_TTerm a)
        |   parse_TTerm (INT) = INT_;
    in
        fun parse_context (context: (string * TTerm) list): ttype context_t.dict = foldl (fn ((l,t),b) => context_t.insert((l,parse_TTerm t),b) ) context_t.empty context;
    end;

    local
        fun substitute var term [] = []
        |   substitute var term ((Var v)::rest) = (if v=var then term else (Var v))::(substitute var term rest)
        |   substitute var term ((Fun (name,tl))::rest) = (Fun (name,substitute var term tl))::(substitute var term rest);

        fun substituteall [] l = l
        |   substituteall ((name,term)::rest) l = substituteall rest (substitute name term l);
    in
        fun typecheck lmterm context = case impl lmterm (parse_context context)
                                        of NONE => NONE
                                        |  SOME(t,subs) => SOME (term_to_TTerm (hd(substituteall subs [TTerm_to_term t])));
    end;
end
