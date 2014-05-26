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
    
    val collect: oset -> Key.t list;
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
        
        fun collect set = let
            val result = ref [];
            fun travel (Empty) = ()
            |   travel (Two(left,x,right)) = (travel left; result := x :: (!result); travel right)
            |   travel (Three(left,x,center,y,right)) = (travel left; result := x ::(!result); travel center; result := y ::(!result); travel right);
            val () = travel set;
        in !result end;
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
    
    structure GenericCmp: COMPARABLE = struct
        type t = string; (* Nazwa generica *)
        fun cmp (a,b) = String.compare(a,b);
    end;
    
    structure context_t = TDict(structure KeyS=LabelCmp);
    structure stringDict_t = TSet(structure KeyS=StringCmp);
    structure genericDict_t = TDict(structure KeyS=GenericCmp);
    structure genericSet_t = TSet(structure KeyS=GenericCmp);

    val namesOfThingsToGeneralize : string list ref = ref [];
    
    fun needGeneralization (name: label) [] = false
    |   needGeneralization name (a::at) = if name=a then true else needGeneralization name at;
    
    type callback_t = label * label -> unit;
    
    datatype ttype = VAR_ of label
                    | GENERIC_ of label * callback_t
                    | ARR_ of ttype * ttype
                    | LIST_ of ttype
                    | INT_;
                    
    fun ttype_to_string (VAR_(l)) : string = concat ["",l,""]
    |   ttype_to_string (GENERIC_(l,_)) = concat ["'",l,""]
    |   ttype_to_string (ARR_(a,b)) = concat ["(",ttype_to_string a," -> ",ttype_to_string b,")"]
    |   ttype_to_string (LIST_(a)) = concat ["[",ttype_to_string a,"]"]
    |   ttype_to_string (INT_) = "INT_";
    
    local
        fun f (label,ttype) : unit = print (concat [label,": ",ttype_to_string ttype,"\n"]);
    in
        fun dump_context context = (context_t.app f context; print "\n");
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
        
    local
        fun substitute var term [] = []
        |   substitute var term ((Var v)::rest) = (if v=var then term else (Var v))::(substitute var term rest)
        |   substitute var term ((Fun (name,tl))::rest) = (Fun (name,substitute var term tl))::(substitute var term rest);

        fun substituteall [] l = l
        |   substituteall ((name,term)::rest) l = substituteall rest (substitute name term l);
        
        fun substitute_in_substitution_atom (label,term) (label2,term2) = (label2,hd(substitute label term [term2]));
        fun substitute_in_substitution ((label,term),(sub: substitution)) : substitution = map (substitute_in_substitution_atom (label,term)) sub;
    in
        fun consumeSubstitution (subs: substitution) (term: TTerm) : TTerm = term_to_TTerm (hd(substituteall subs [TTerm_to_term term]));
        fun fillSubstitution (sub: substitution) : substitution = foldl substitute_in_substitution sub sub;
    end;
    
    local
        fun term_to_string (Var(l)) : string = implode l
        |   term_to_string (Fun(name,terms)) = concat [implode name,"(",(String.concatWith "," (map term_to_string terms)),")"];
        
        fun line (label, term) : unit = print (concat [implode label," = ",term_to_string term,"\n"]);
    in
        fun dump_substitution (substitution: substitution) : unit = (app line (fillSubstitution substitution); print "\n");
        fun dump_termsPair (left,right) : unit = (ListPair.app (fn (a,b) => print (concat [" ",term_to_string a," = ",term_to_string b,"\n"])) (left,right); print "\n");
    end;
    
    local
        val instance_count = ref 0;
    
        fun make_new_instance_name l = let
            val result = concat [l,"_",Int.toString (!instance_count)];
            val () = namesOfThingsToGeneralize:=  (result::(!namesOfThingsToGeneralize));
            in result end;
        fun impl ((INT_): ttype) : TTerm = INT
        |   impl (VAR_ l) = VAR l
        |   impl (GENERIC_ (l,f)) = let
            val name = (make_new_instance_name l);
            val () = f(l,name);
        in VAR(name) end
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
            val () = namesOfThingsToGeneralize := result::(!namesOfThingsToGeneralize);
        in result end;
    end;
    
    fun substitution_to_termLists sub = foldr (fn ((n,t),(l,r)) => ((Var n)::l,t::r)) ([],[]) sub;
    
    fun add_tterm_to_context (name: label) (term: ttype) context = context_t.insert((name,term),context);

    fun makeTypeVariablesForLetInContext [] context = context
    |   makeTypeVariablesForLetInContext ((label,_)::rest) context = let
        val new_variable = VAR_ (get_new_type_variable_name ());
    in makeTypeVariablesForLetInContext rest (add_tterm_to_context label new_variable context) end;
    
    local
        fun generalizeIfNecessary (callback: callback_t) namesToGeneralize (VAR_(n)) = if needGeneralization n namesToGeneralize then (print (concat ["Generalizuje ",n,"\n"]); GENERIC_(n,callback)) else VAR_(n)
        |   generalizeIfNecessary callback namesToGeneralize (GENERIC_(n,f)) = GENERIC_(n,f)
        |   generalizeIfNecessary callback namesToGeneralize (ARR_(a,b)) = ARR_(generalizeIfNecessary callback namesToGeneralize a,generalizeIfNecessary callback namesToGeneralize b)
        |   generalizeIfNecessary callback namesToGeneralize (LIST_(a)) = LIST_(generalizeIfNecessary callback namesToGeneralize a)
        |   generalizeIfNecessary callback namesToGeneralize (INT_) = INT_;
        
        fun trans namesToGeneralize (callback: callback_t) (key,value) = (key,generalizeIfNecessary callback namesToGeneralize value);
    in
        fun generalizeContextWithHint context (callback: callback_t) namesToGeneralize = (print (concat ["Do generalizacji: ",String.concatWith ", " namesToGeneralize,"\n"]); context_t.transform (trans namesToGeneralize callback) context);
    end;
    
    local
        fun wrap namesOfThingsToGeneralize callback (VAR(n)) = if needGeneralization n namesOfThingsToGeneralize then GENERIC_(n,callback) else VAR_(n)
        |   wrap namesOfThingsToGeneralize callback (ARR(a,b)) = ARR_(wrap namesOfThingsToGeneralize callback a,wrap namesOfThingsToGeneralize callback b)
        |   wrap namesOfThingsToGeneralize callback (LIST(a)) = LIST_(wrap namesOfThingsToGeneralize callback a)
        |   wrap namesOfThingsToGeneralize callback (INT) = INT_;
        fun consumeOne substitution namesOfThingsToGeneralize callback ((label,_),context) = context_t.insert((label,wrap namesOfThingsToGeneralize callback (consumeSubstitution substitution (valOf (get_label_instance label context)))),context);
    in
        fun consumeSubstitutionForLabelToTermList labelToTermList (substitution: substitution) context namesOfThingsToGeneralize callback = foldl (consumeOne substitution namesOfThingsToGeneralize callback) context labelToTermList;
    end;
    
    local
        fun collect_generic_names_from_term (collection: genericSet_t.oset ref) gen_to_inst (VAR(l)) : unit = (case genericDict_t.lookup(l,gen_to_inst)
                                                                                                                of NONE => ()
                                                                                                                |  SOME(_) => let
                                                                                                                    val newCollection = genericSet_t.insert(l,!collection);
                                                                                                                    val () = collection := newCollection;
                                                                                                                in () end)
        | collect_generic_names_from_term collection gen_to_inst (ARR(a,b)) = let
            val () = collect_generic_names_from_term collection gen_to_inst a;
            val () = collect_generic_names_from_term collection gen_to_inst b;
            in () end
        | collect_generic_names_from_term collection gen_to_inst (LIST(a)) = collect_generic_names_from_term collection gen_to_inst a
        | collect_generic_names_from_term collection gen_to_inst (INT) = ();
        fun generic_names_from_term_pair (term1,term2) gen_to_inst = let
            val col = ref genericSet_t.empty;
            val () = collect_generic_names_from_term col gen_to_inst term1;
            val () = collect_generic_names_from_term col gen_to_inst term2;
        in genericSet_t.collect(!col) end;
        
        fun substitute_name_for_name (VAR(l)) from to = if l=from then VAR(to) else VAR(l)
        |   substitute_name_for_name (ARR(a,b)) from to = ARR(substitute_name_for_name a from to, substitute_name_for_name b from to)
        |   substitute_name_for_name (LIST(a)) from to = LIST(substitute_name_for_name a from to)
        |   substitute_name_for_name (INT) from to = INT;
        
        fun all_substitutions_for_name term gen_to_inst name = map (substitute_name_for_name term name) (valOf(genericDict_t.lookup(name,gen_to_inst)));
        
        fun substitute_generics_in_term gen_to_inst [] (term: TTerm) = [term]
        |   substitute_generics_in_term gen_to_inst (name::rest) term = List.concat (map (substitute_generics_in_term gen_to_inst rest) (all_substitutions_for_name term gen_to_inst name));
        fun instantiate_subs_in_one_equation leftTerm rightTerm gen_to_inst = let
            val names = generic_names_from_term_pair (leftTerm,rightTerm) gen_to_inst;
            val leftResult = substitute_generics_in_term gen_to_inst names leftTerm;
            val rightResult = substitute_generics_in_term gen_to_inst names rightTerm;
        in (leftResult,rightResult) end;
        (* 1 Zebrać nazwy genericów z termu
           2 Dla każdej nazwy zrobić wszystkie podstawienia
           3 Zwrócić *)
           
        fun impl (leftTerms,rightTerms) gen_to_inst = let
            fun aux (leftTerm,rightTerm,(resultLeft,resultRight)) = let
                val (left,right) = instantiate_subs_in_one_equation leftTerm rightTerm gen_to_inst;
            in (left@resultLeft,right@resultRight) end;
            val (left,right) = ListPair.foldl aux ([],[]) (map term_to_TTerm leftTerms,map term_to_TTerm rightTerms);
            val () = dump_termsPair (map TTerm_to_term left,map TTerm_to_term right);
        in U.lunify(SOME((map TTerm_to_term left,map TTerm_to_term right))) end;
    in
        fun make_substitution_with_generics_instantiated (substitution: substitution) (generic_to_instance_list: label list genericDict_t.dict) : substitution option = impl (substitution_to_termLists substitution) generic_to_instance_list;
    end;
    
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
                    in (case resultSubstitution of NONE => NONE | SOME(s) => SOME(consumeSubstitution s new_variable,s)) end)) end
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
            in case resultSubstitution of NONE => NONE | SOME(s) => SOME(consumeSubstitution s result_variable,s) end end
    |   impl (Let (labelToTermList, body)) context = let
        val (substitution,new_context,generic_to_inst_list) = handleLetDefinitions labelToTermList context;
    in case substitution of NONE => NONE | SOME(ss) => let
        val (substitutionL,substitutionR) = substitution_to_termLists ss;
        in case impl body new_context
            of NONE => NONE
            |  SOME(upperType,subs) => let
                val (subsL,subsR) = substitution_to_termLists subs;
                val () = dump_substitution ss;
                val () = dump_substitution subs;
(*                 val result_substitution = make_substitution_with_generics_instantiated (ss@subs) (!generic_to_inst_list); *)
                val result_substitution = U.lunify (SOME (substitutionL @ subsL, substitutionR @ subsR));
                val () = dump_substitution (valOf result_substitution);
            in case result_substitution of NONE => NONE | SOME(s) => SOME(consumeSubstitution s upperType,s) end end end
    and handleLetDefinitions labelToTermList context : substitution option * ttype context_t.dict * label list genericDict_t.dict ref = let

        val new_context = makeTypeVariablesForLetInContext labelToTermList context; (* Tworzy nowe zmienne typowe i umieszcza je w kontekście *)
(*         val () = dump_context new_context; *)
        val namesOfThingsToGeneralizeBackup = !namesOfThingsToGeneralize; (* Przywrócić po zakończeniu *)
        val () = namesOfThingsToGeneralize := [];
        val new_substitution = makeSubstitutionForLet labelToTermList new_context; (* Tworzy podstawienie nowych zmiennych typowych do typów poszczególnych termów w LET *)
    in case new_substitution of NONE => (NONE,new_context,ref genericDict_t.empty) | SOME(s) => let
        val generic_to_instance_list = ref genericDict_t.empty;
        fun callback (generic_label,var_label) = let
            val instance_list = case genericDict_t.lookup(generic_label,!generic_to_instance_list)
                                    of NONE => []
                                    |  SOME(l) => l
            val instance_list_final = var_label::instance_list;
            val result = genericDict_t.insert((generic_label,instance_list_final),!generic_to_instance_list);
            val () = generic_to_instance_list := result;
            in () end;
        val new_context2 = consumeSubstitutionForLabelToTermList labelToTermList s new_context (!namesOfThingsToGeneralize) callback;
        val () = dump_context new_context2;
(*         val generalized_context = generalizeContextWithHint new_context2 callback (!namesOfThingsToGeneralize); (* Generalizuje zmienne w kontekście wymienione (z nazwy) w danym zbiorze *) *)
(*         val () = dump_context generalized_context; *)
        val () = namesOfThingsToGeneralize := namesOfThingsToGeneralizeBackup;
    in (new_substitution,new_context2,generic_to_instance_list) end end
    and makeSubstitutionForLet labelToTermList context : substitution option = let
        fun handleOneLabelToTerm (_,NONE) = NONE
        |   handleOneLabelToTerm ((label, term),SOME(sub)) = case impl term context
            of NONE => NONE
            |  SOME(parsedType,parsedSubs) => let
                val (subsL,subsR) = substitution_to_termLists (sub @ parsedSubs);
(*                 val (parsedL,parsedR) = substitution_to_termLists parsedSubs; *)
                val left = TTerm_to_term (valOf (get_label_instance label context));
                val right = TTerm_to_term parsedType;
                val result = U.lunify(SOME(subsL@[left],subsR@[right]));
(*                 val result = U.lunify(SOME(subsL@parsedL@[left],subsR@parsedR@[right])); *)
            in result end;
    in foldl handleOneLabelToTerm (SOME([])) labelToTermList end;
            
        (* handleLetDefinitions: uwzględniając obsługe generalizacji sparsować LET, zgeneralizować
        to co trzeba i zwrócić podstawienie oraz nowy kontekst *)
    
    local       (* Generalizuje TTerm do ttype *)
        fun nop_callback _ = ();
    
        fun parse_TTerm ((VAR label): TTerm) : ttype = GENERIC_ (label,nop_callback)
        |   parse_TTerm (ARR (a,b)) = ARR_ (parse_TTerm a, parse_TTerm b)
        |   parse_TTerm (LIST a) = LIST_ (parse_TTerm a)
        |   parse_TTerm (INT) = INT_;
    in
        fun parse_context (context: (string * TTerm) list): ttype context_t.dict = foldl (fn ((l,t),b) => context_t.insert((l,parse_TTerm t),b) ) context_t.empty context;
    end;

    fun typecheck lmterm context = case impl lmterm (parse_context context)
                                    of NONE => NONE
                                    |  SOME(t,subs) => SOME (consumeSubstitution subs t);
end
