
signature COMPARABLE = sig
        type t;
        val cmp: t*t -> order   
end;

signature DICT= sig
        structure Key:COMPARABLE;

        type 'vt dict;

        val empty: 'vt dict;
        val insert: (Key.t * 'vt) * 'vt dict -> 'vt dict
        val lookup: (Key.t * 'vt dict) -> 'vt option            
end;

signature OSET= sig
        structure Key:COMPARABLE;

        type oset;

        val empty: oset;
        val insert: Key.t * oset -> oset
        val member: Key.t * oset -> bool        
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

functor TDict(structure KeyS:COMPARABLE):>DICT where type Key.t=KeyS.t = struct
        structure Spec:SPEC=DSpec(structure KeyS=KeyS);
        structure Frame= TFrame(structure Spec= Spec);

        structure Key:COMPARABLE=KeyS;
        type 'vt dict= 'vt Frame.frame;

        val empty= Frame.empty;
        val insert= Frame.insert;
        val lookup= Frame.lookup;       
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

local

datatype term_meta_info = Var_ of string (* Zachowana nazwa *)
                        | Fun_ of string * int list; (* Zachowana nazwa, arność funkcji *)

datatype term_meta_name = Var__ of string | Fun__ of string;
                        
datatype node = 
    Node of int (* class pointer *)
          * int (* size of the class - na potrzeby find-union *)
          * term (* schema term *)
          * term_meta_info (* term rozbity na kawałki - identyfikatory zamiast sub termów *)
          * bool (* visited *)
          * bool (* acyclic *)
          * name list (* vars - jako nazwy zmiennych *)
          ;

structure c_term_meta_info: COMPARABLE= struct
        type t= term_meta_name;
        fun cmp ((Var__(a)),(Var__(b))) = String.compare(a,b)
        |   cmp ((Var__(_)),(Fun__(_))) = LESS
        |   cmp ((Fun__(_)),(Var__(_))) = GREATER
        |   cmp ((Fun__(a)),(Fun__(b))) = String.compare(a,b);
end;

structure cInt: COMPARABLE= struct
        type t= int;
        val cmp= Int.compare;
end;

structure term_meta_info_dict_t= TDict(structure KeyS=c_term_meta_info);
structure id_to_term_dict_t = TDict(structure KeyS=cInt);

fun convert_term_to_meta (Var(name)) : (term_meta_name*int) = (Var__(implode name),(~1))
|   convert_term_to_meta (Fun(name,args)) = (Fun__(implode name),length args);

fun get_next_id (next_id: int ref) = let
    val result = !next_id;
    val () = next_id := result+1;
    in result end;

(* Tworzy jeśli trzeba i zwraca identyfikator danego termu. Nie powiedzie się, jeżeli arność 
   symboli funkcyjnych nie jest zachowana. *)
fun get_node_id (mapping,rev_mapping,next_id, term) : int option = let
    val (term_meta,arity) = convert_term_to_meta term;
    in case term_meta_info_dict_t.lookup(term_meta,!mapping)
        of SOME(id,f_arity) => if arity <> f_arity then NONE else SOME(id)
        |  NONE => (case term
                    of Var(name) => let
                        val id = get_next_id next_id;
                        val new_mapping = term_meta_info_dict_t.insert((term_meta,(id,~1)),!mapping);
                        val () = mapping := new_mapping;
                        val new_rev_mapping = id_to_term_dict_t.insert((id,term),!rev_mapping);
                        val () = rev_mapping := new_rev_mapping;
                        in SOME(id) end
                    |  Fun(name,args) => let
                        val id = get_next_id next_id;
                        val new_mapping = term_meta_info_dict_t.insert((term_meta,(id,arity)),!mapping);
                        val () = mapping := new_mapping;
                        val new_rev_mapping = id_to_term_dict_t.insert((id,term),!rev_mapping);
                        val () = rev_mapping := new_rev_mapping;
                        val to_check = map (fn (a) => get_node_id (mapping,rev_mapping,next_id,a)) args;
                        val succeed = List.exists (fn (a) => case a of NONE => true | _ => false) to_check;
                        in if succeed then SOME(id) else NONE end
        
        ) end;

(* Zwraca identyfikator danego termu. *)
fun get_node_id_const (mapping: (int * int) term_meta_info_dict_t.dict) term : int = let
    val (term_meta,arity) = convert_term_to_meta term;
    in #1 (valOf (term_meta_info_dict_t.lookup(term_meta,mapping))) end;
        
fun build_node (mapping,rev_mapping,id) = let
    val term = valOf (id_to_term_dict_t.lookup(id,rev_mapping));
    in Node(
        id,
        1,
        term,
        case term of Var(name) => Var_(implode name) | Fun(name,args) => Fun_(implode name,map (get_node_id_const mapping) args),
        false,
        false,
        case term of Var(name) => [name] | _ => []) end;
        
fun build_node_array (mapping,rev_mapping,id,end_id) = if id<>end_id then ref (build_node(mapping,rev_mapping,id)) :: (build_node_array(mapping,rev_mapping,id+1,end_id)) else [];
        
fun build_graph ((term1: term),(term2: term)) : node vector option = let
    val mapping = ref term_meta_info_dict_t.empty;
    val rev_mapping = ref id_to_term_dict_t.empty;
    val id_gen = ref 0;
in case get_node_id (mapping,rev_mapping,id_gen,term1) of NONE => NONE | SOME(term1_id) =>
   case get_node_id (mapping,rev_mapping,id_gen,term2) of NONE => NONE | SOME(term2_id) =>
    
    
    NONE end;
          
in

fun unify (term1: term) (term2: term) : substitution option = let
    val G = build_graph(term1,term2);
    in NONE end;

    
end; (* local *)