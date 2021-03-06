signature COMPARABLE = sig
        type t;
        val cmp: t*t -> order;
end;

signature OSET= sig
    structure Key:COMPARABLE;

    type oset;

    val empty: oset;
    val insert: Key.t * oset -> oset
    val member: Key.t * oset -> bool
end;

signature DICT= sig
    structure Key:COMPARABLE;

    type 'vt dict;

    val empty: 'vt dict;
    val insert: (Key.t * 'vt) * 'vt dict -> 'vt dict;
    val lookup: (Key.t * 'vt dict) -> 'vt option;

    val transform: (Key.t * 'vt -> Key.t * 'vt) -> 'vt dict -> 'vt dict;
    val app: (Key.t * 'vt -> unit) -> 'vt dict -> unit;
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

datatype 'a result = Single of 'a node (* w??ze?? *)
|                    Double of 'a * 'a node * 'a node; (* warto????, lewy, prawy *)

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

functor SSpec (structure KeyS:COMPARABLE):SPEC = struct
        structure Key:COMPARABLE = KeyS;
        type 'vT entryT = KeyS.t;
        type 'vT resultT = bool;

        fun extractKey key = key;
        fun updateE (T,x) =
            case impl (fn (x,y) => KeyS.cmp (x,y)) (x, T) of Single (n) => Good(n)
            |                       Double (n, left, right) => PropagateUp( Two(left, n, right));
        fun lookupE (NONE) = false
        |   lookupE (SOME(_)) = true;
end;

functor TSet(structure KeyS:COMPARABLE):>OSET where type Key.t=KeyS.t = struct
        structure Spec:SPEC=SSpec(structure KeyS=KeyS);
        structure Frame= TFrame(structure Spec= Spec);

        structure Key:COMPARABLE=KeyS;
        type oset= unit Frame.frame;

        val empty= Frame.empty;
        val insert= Frame.insert;
        val member= Frame.lookup;
end;

functor TDict(structure KeyS:COMPARABLE):>DICT where type Key.t=KeyS.t = struct
    structure Spec:SPEC=DSpec(structure KeyS=KeyS);
    structure Frame= TFrame(structure Spec= Spec);

    structure Key:COMPARABLE=KeyS;
    type 'vt dict= 'vt Frame.frame;

    val empty= Frame.empty;
    val insert= Frame.insert;
    val lookup= Frame.lookup;

    fun transform f (Empty) = Empty
    |   transform f (Two(left,x,right)) = Two(transform f left, f x, transform f right)
    |   transform f (Three(left,x,center,y,right)) = Three(transform f left, f x, transform f center, f y, transform f right);

    fun app f (Empty) = ()
    |   app f (Two(left,x,right)) = (app f left; f x; app f right)
    |   app f (Three(left,x,center,y,right)) = (app f left; f x; app f center; f y; app f right);
    
end;

functor TYPECHECK(U:UNIFIER) = struct
(*     Implementacja     *)

    structure LabelCmp: COMPARABLE = struct
        type t = label;
        fun cmp (a,b) = String.compare(a,b);
    end;

    structure StringCmp: COMPARABLE = struct
        type t = string;
        fun cmp (a,b) = String.compare(a,b);
    end;

    structure context_t = TDict(structure KeyS=LabelCmp);
    structure labelSet_t = TSet(structure KeyS=LabelCmp);
    structure stringDict_t = TSet(structure KeyS=StringCmp);

    val namesOfThingsToGeneralize : string list ref = ref [];

    fun needGeneralization (name: label) toGeneralize notToGeneralize = (List.exists (fn x => x=name) toGeneralize) andalso (not (labelSet_t.member (name,notToGeneralize)));

    datatype ttype = VAR_ of label
                    | GENERIC_ of label
                    | ARR_ of ttype * ttype
                    | LIST_ of ttype
                    | INT_;

    local
        val instance_count = ref 0;

        fun make_new_instance_name l = let
            val result = concat [l,"_",Int.toString (!instance_count)];
            val () = namesOfThingsToGeneralize:=  (result::(!namesOfThingsToGeneralize));
            in result end;
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
        
        fun reset_instance_names () = let
            val () = instance_count := 0;
            val () = namesOfThingsToGeneralize := [];
            in () end;
    end;

    (* Tworzy now?? instancje na podstawie wybranego schematu typu z kontekstu *)
    fun get_label_instance (l:label) (context: ttype context_t.dict) = case context_t.lookup(l,context)
                                                                of NONE => NONE
                                                                |  SOME(t) => SOME (instantiate t);
                                                                
    fun get_label (l:label) (context: ttype context_t.dict) = valOf (context_t.lookup(l,context));

    local
        val count = ref 0;
    in
        fun get_new_type_variable_name () = let
            val result = Int.toString (!count);
            val () = count := (!count) + 1;
            val () = namesOfThingsToGeneralize := result::(!namesOfThingsToGeneralize);
        in result end;
        
        fun reset_type_variable_generator () : unit = count := 0;
    end;

    (* Konwertuje TTerm do term na potrzeby unifikacji *)
    fun TTerm_to_term (VAR l) = Var (explode l)
    |   TTerm_to_term (ARR (a,b)) = Fun ((explode "ARR"), map TTerm_to_term [a,b])
    |   TTerm_to_term (LIST (a)) = Fun ((explode "LIST"), [TTerm_to_term a])
    |   TTerm_to_term (INT) = Fun ((explode "INT"),[]);

    (* Konwertuje term do TTerm aby powr??ci?? z unifikacji do formatu wyj??ciowego *)
    fun term_to_TTerm (Var name) = VAR (implode name)
    |   term_to_TTerm (Fun (name, termList)) = case implode name
                                                of "ARR" => ARR (term_to_TTerm (hd termList), term_to_TTerm (hd(tl termList)))
                                                |  "LIST" => LIST (term_to_TTerm (hd termList))
                                                |  "INT" => INT;

    fun substitution_to_termLists sub = foldr (fn ((n,t),(l,r)) => ((Var n)::l,t::r)) ([],[]) sub;

    fun add_tterm_to_context (name: label) (term: ttype) context = context_t.insert((name,term),context);

    fun makeTypeVariablesForLetInContext [] context = context
    |   makeTypeVariablesForLetInContext ((label,_)::rest) context = let
        val new_variable = VAR_ (get_new_type_variable_name ());
    in makeTypeVariablesForLetInContext rest (add_tterm_to_context label new_variable context) end;

    local
        fun generalizeIfNecessary namesToGeneralize varsNotToGeneralize (VAR_(n)) = if needGeneralization n namesToGeneralize varsNotToGeneralize then GENERIC_(n) else VAR_(n)
        |   generalizeIfNecessary namesToGeneralize varsNotToGeneralize (GENERIC_(n)) = GENERIC_(n)
        |   generalizeIfNecessary namesToGeneralize varsNotToGeneralize (ARR_(a,b)) = ARR_(generalizeIfNecessary namesToGeneralize varsNotToGeneralize a,generalizeIfNecessary namesToGeneralize varsNotToGeneralize b)
        |   generalizeIfNecessary namesToGeneralize varsNotToGeneralize (LIST_(a)) = LIST_(generalizeIfNecessary namesToGeneralize varsNotToGeneralize a)
        |   generalizeIfNecessary namesToGeneralize varsNotToGeneralize (INT_) = INT_;

        fun trans namesToGeneralize varsNotToGeneralize (key,value) = (key,generalizeIfNecessary namesToGeneralize varsNotToGeneralize value);
    in
        fun generalizeContextWithHint context namesToGeneralize varsNotToGeneralize = context_t.transform (trans namesToGeneralize varsNotToGeneralize) context;
    end;

    local
        fun substitute var term [] = []
        |   substitute var term ((Var v)::rest) = (if v=var then term else (Var v))::(substitute var term rest)
        |   substitute var term ((Fun (name,tl))::rest) = (Fun (name,substitute var term tl))::(substitute var term rest);

        fun substituteall [] l = l
        |   substituteall ((name,term)::rest) l = substituteall rest (substitute name term l);
        
        fun ttype_to_TTerm (VAR_(n)) = VAR(n)
        |   ttype_to_TTerm (GENERIC_(_)) = VAR("__")
        |   ttype_to_TTerm (ARR_(a,b)) = ARR(ttype_to_TTerm a, ttype_to_TTerm b)
        |   ttype_to_TTerm (LIST_(a)) = LIST(ttype_to_TTerm a)
        |   ttype_to_TTerm (INT_) = INT;
    in
        fun consumeSubstitution (subs: substitution) (term: TTerm) : TTerm = term_to_TTerm (hd(substituteall subs [TTerm_to_term term]));
        fun apply_substitution subs term = consumeSubstitution subs (ttype_to_TTerm term);
    end;

    local
        fun wrap (VAR(n)) = VAR_(n)
        |   wrap (ARR(a,b)) = ARR_(wrap a,wrap b)
        |   wrap (LIST(a)) = LIST_(wrap a)
        |   wrap (INT) = INT_;
        fun consumeOne substitution ((label,_),context) = context_t.insert((label,wrap (consumeSubstitution substitution (valOf (get_label_instance label context)))),context);
    in
        fun consumeSubstitutionForLabelToTermList labelToTermList (substitution: substitution) context = foldl (consumeOne substitution) context labelToTermList;
    end;
    
    
    fun getVars (VAR_(n)) = [n]
    |   getVars (GENERIC_(n)) = []
    |   getVars (ARR_(a,b)) = getVars a @ (getVars b)
    |   getVars (LIST_(a)) = getVars a
    |   getVars (INT_) = []
    
    fun collect_var_names (VAR(n)) result = if not (n="__") then let
        val new_result = labelSet_t.insert(n,(!result));
        val () = result := new_result
        in () end else ()
    |   collect_var_names (ARR(a,b)) result = (collect_var_names a result; (collect_var_names b result))
    |   collect_var_names (LIST(a)) result = collect_var_names a result
    |   collect_var_names (INT) result = ();
    
    fun getNamesNotToGeneralize context substitution [] result = ()
    |   getNamesNotToGeneralize context substitution (label::rest) result = let
        val type1 = get_label label context;
        val type2 = apply_substitution substitution type1;
        val () = collect_var_names type2 result;
        in getNamesNotToGeneralize context substitution rest result end;

    fun impl (Number _) context : (TTerm*term list*term list) option = SOME(INT,[],[])
    |   impl (Label label) context = (case get_label_instance label context
                                        of NONE => NONE
                                        |  SOME(t) => SOME((t,[],[])))
    |   impl (App (a,b)) context = let
            val aResult = impl a context;
            val bResult = impl b context;
        in (case aResult
            of NONE => NONE
            |  SOME(aType, al, ar) =>
                (case bResult
                 of NONE => NONE
                 |  SOME(bType, bl, br) => let
                        val new_variable = VAR (get_new_type_variable_name ());
(*                         val (al,ar) = substitution_to_termLists aSubstitution; *)
(*                         val (bl,br) = substitution_to_termLists bSubstitution; *)
                        val newL = TTerm_to_term aType;
                        val newR = TTerm_to_term (ARR (bType,new_variable));
                        val leftTerms = newL :: al @ bl;
                        val rightTerms = newR :: ar @ br;
(*                         val resultSubstitution = U.lunify (SOME (leftTerms,rightTerms)); *)
                    in (SOME(new_variable,leftTerms,rightTerms)) end)) end
    |   impl (Abs (l,t)) context = let
            val new_variable = VAR_ (get_new_type_variable_name ());
            val new_context = add_tterm_to_context l new_variable context;
        in case impl t new_context
            of NONE => NONE
            |  SOME(upperType,upperL,upperR) => let
                val result_variable = VAR (get_new_type_variable_name ());
(*                 val (upperL,upperR) = substitution_to_termLists subs; *)
                val newL = TTerm_to_term result_variable;
                val newR = TTerm_to_term (ARR (valOf (get_label_instance l new_context),upperType));
                val leftTerms = newL :: upperL;
                val rightTerms = newR :: upperR;
(*                 val resultSubstitution = U.lunify (SOME (leftTerms,rightTerms)); *)
            in SOME(result_variable,leftTerms,rightTerms) end end
    |   impl (Let (labelToTermList, body)) context = let
        val (substitution,new_context) = handleLetDefinitions labelToTermList context;
    in case substitution of NONE => NONE | SOME(ss) => let
        val (substitutionL,substitutionR) = substitution_to_termLists ss;
        in case impl body new_context
            of NONE => NONE
            |  SOME(upperType,subsL,subsR) => let
(*                 val (subsL,subsR) = substitution_to_termLists subs; *)
(*                 val resultSubstitution = U.lunify (SOME (substitutionL @ subsL, substitutionR @ subsR)); *)
            in SOME(upperType,substitutionL @ subsL, substitutionR @ subsR) end end end
    and handleLetDefinitions labelToTermList context = let
        val namesOfThingsToGeneralizeBackup = !namesOfThingsToGeneralize; (* Przywr??ci?? po zako??czeniu *)
        val () = namesOfThingsToGeneralize := [];
        val varsNotToGeneralize = ref [];
        fun appFun (label,value) = let
            val result = label :: (!varsNotToGeneralize);
(*             val result = getVars value @ (!varsNotToGeneralize); *)
            val () = varsNotToGeneralize := result;
            in () end;
        val () = context_t.app appFun context;
(*         val () = print (String.concatWith ", " (!varsNotToGeneralize) ^ "\n"); *)
        val new_context = makeTypeVariablesForLetInContext labelToTermList context; (* Tworzy nowe zmienne typowe i umieszcza je w kontek??cie *)
        val new_unif_problem = makeSubstitutionForLet labelToTermList new_context; (* Tworzy podstawienie nowych zmiennych typowych do typ??w poszczeg??lnych term??w w LET *)
        val new_substitution = U.lunify(new_unif_problem);
    in case new_substitution of NONE => (NONE,new_context) | SOME(s) => let
        val new_context2 = consumeSubstitutionForLabelToTermList labelToTermList s new_context;
        val namesNotToGeneralize = ref labelSet_t.empty;
        val () = getNamesNotToGeneralize new_context2 s (!varsNotToGeneralize) namesNotToGeneralize;
(*         val () = print (String.concatWith ", " namesNotToGeneralize^"\n"); *)
        val generalized_context = generalizeContextWithHint new_context2 (!namesOfThingsToGeneralize) (!namesNotToGeneralize); (* Generalizuje zmienne w kontek??cie wymienione (z nazwy) w danym zbiorze *)
        val () = namesOfThingsToGeneralize := namesOfThingsToGeneralizeBackup;
    in (new_substitution,generalized_context) end end
    and makeSubstitutionForLet labelToTermList context = let
        fun handleOneLabelToTerm (_,NONE) = NONE
        |   handleOneLabelToTerm ((label, term),SOME(subsL,subsR)) = case impl term context
            of NONE => NONE
            |  SOME(parsedType,parsedL,parsedR) => let
(*                 val (subsL,subsR) = substitution_to_termLists sub; *)
(*                 val (parsedL,parsedR) = substitution_to_termLists parsedSubs; *)
                val left = TTerm_to_term (valOf (get_label_instance label context));
                val right = TTerm_to_term parsedType;
(*                 val result = U.lunify(SOME(subsL@parsedL@[left],subsR@parsedR@[right])); *)
            in SOME(left::parsedL@subsL,right::parsedR@subsR) end;
    in foldl handleOneLabelToTerm (SOME([],[])) labelToTermList end;

        (* handleLetDefinitions: uwzgl??dniaj??c obs??uge generalizacji sparsowa?? LET, zgeneralizowa??
        to co trzeba i zwr??ci?? podstawienie oraz nowy kontekst *)

    local       (* Generalizuje TTerm do ttype *)
        fun parse_TTerm ((VAR label): TTerm) : ttype = GENERIC_ label
        |   parse_TTerm (ARR (a,b)) = ARR_ (parse_TTerm a, parse_TTerm b)
        |   parse_TTerm (LIST a) = LIST_ (parse_TTerm a)
        |   parse_TTerm (INT) = INT_;
    in
        fun parse_context (context: (string * TTerm) list): ttype context_t.dict = foldl (fn ((l,t),b) => context_t.insert((l,parse_TTerm t),b) ) context_t.empty context;
    end;

    fun typecheck lmterm context = let
        val () = reset_instance_names ();
        val () = reset_type_variable_generator ();
        in
        case impl lmterm (parse_context context)
                                    of NONE => NONE
                                    |  SOME(t,left,right) => (case U.lunify(SOME(left,right))
                                                                of SOME(s) => SOME (consumeSubstitution s t)
                                                                |  NONE => NONE) end;
end
