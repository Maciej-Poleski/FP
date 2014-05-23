
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
                        
datatype term_with_id = Var__ of int * term  (* Współdzielony identyfikator + term *)
                      | Fun__ of int * term_with_id list * term (* Unikalny identyfikator + identyfikatory argumentów + term *)
                        
fun get_id (Var__(id,_)) = id
|   get_id (Fun__(id,_,_)) = id;
                        
datatype node = 
    Node of int (* class pointer *)
          * int (* size of the class - na potrzeby find-union *)
          * term (* schema term *)
          * term_meta_info (* term rozbity na kawałki - identyfikatory zamiast sub termów *)
          * bool (* visited *)
          * bool (* acyclic *)
          * name list (* vars - jako nazwy zmiennych *)
          ;

fun get_term_meta_info (Node(_,_,_,r,_,_,_)) = r;
fun get_size (Node(_,r,_,_,_,_,_)) = r;
fun get_schema (Node(_,_,r,_,_,_,_)) = r;
fun get_class (Node(r,_,_,_,_,_,_)) = r;
fun get_acyclic (Node(_,_,_,_,_,r,_)) = r;
fun get_visited (Node(_,_,_,_,r,_,_)) = r;

fun node_with_size_vars_schema_meta (Node(a,_,_,_,e,f,_)) size vars schema meta = Node(a,size,schema,meta,e,f,vars);
fun node_with_class (Node(_,b,c,d,e,f,g)) class = Node(class,b,c,d,e,f,g);
fun node_with_visited (Node(a,b,c,d,_,f,g)) visited = Node(a,b,c,d,visited,f,g);
fun node_with_acyclic (Node(a,b,c,d,e,_,g)) acyclic = Node(a,b,c,d,e,acyclic,g);

fun for_each_var (Node(_,_,_,_,_,_,vars)) f = app f vars;

fun concat_vars ((Node(_,_,_,_,_,_,a)),(Node(_,_,_,_,_,_,b))) = a@b;
          
structure cInt: COMPARABLE= struct
        type t= int;
        val cmp= Int.compare;
end;

structure cString: COMPARABLE= struct
    type t= string;
    val cmp = String.compare;
end;

structure var_dict_t= TDict(structure KeyS=cString);
structure id_to_term_dict_t = TDict(structure KeyS=cInt);

fun get_next_id (next_id: int ref) = let
    val result = !next_id;
    val () = next_id := result+1;
    in result end;

fun revrite_term (vars,id_generator,rev_mapping) (Var(name)) : term_with_id =
    (case var_dict_t.lookup(implode name,!vars) 
        of SOME(id) => Var__(id,Var(name))
         | NONE => let
             val id = id_generator();
             val name_s = implode name;
             val new_vars = var_dict_t.insert((name_s,id),!vars);
             val () = vars := new_vars;
             val result=Var__(id,Var(name));
             val new_rev_mapping = id_to_term_dict_t.insert((id,result),!rev_mapping);
             val () = rev_mapping := new_rev_mapping;
             in result end)
|   revrite_term (vars,id_generator,rev_mapping) (Fun(name,args)) = let
    val id = id_generator();
    val name_s = implode name;
    val result=Fun__(id,map (revrite_term (vars,id_generator,rev_mapping)) args,Fun(name,args));
    val new_rev_mapping = id_to_term_dict_t.insert((id,result),!rev_mapping);
    val () = rev_mapping := new_rev_mapping;
    in result end;
    
fun revrite_terms (int_get,rev_mapping,term1,term2) = let
    val vars = ref var_dict_t.empty;
    val id_gen = fn () => get_next_id int_get;
    in (revrite_term (vars,id_gen,rev_mapping) term1, revrite_term (vars,id_gen,rev_mapping) term2) end;
        
fun build_node (rev_mapping,id) = 
    case valOf (id_to_term_dict_t.lookup(id,rev_mapping))
    of Var__(_,term) =>
        Node(
        id,
        1,
        term,
        (case term of Var(name) => Var_(implode name)),
        false,
        false,
        [case term of Var(name) => name])
    |  Fun__(_,argsWithIds,term) =>
        Node(
        id,
        1,
        term,
        (case term of Fun(name,_) => Fun_(implode name,map get_id argsWithIds)),
        false,
        false,
        [])
        
fun build_node_array (rev_mapping,id,end_id) = if id<>end_id then ref (build_node(rev_mapping,id)) :: (build_node_array(rev_mapping,id+1,end_id)) else [];
        
fun build_graph ((term1: term),(term2: term)) : (node ref vector *int *int) = let
    val rev_mapping = ref id_to_term_dict_t.empty;
    val id_gen = ref 0;
    val (term1r,term2r) = revrite_terms(id_gen,rev_mapping,term1,term2);
    val node_array = build_node_array(!rev_mapping,0,!id_gen);
    
    in (Vector.fromList node_array,get_id term1r,get_id term2r) end;
          
in

fun unify (term1: term) (term2: term) : substitution option = let
    val (G,t1id,t2id) = build_graph(term1,term2);
    val result = ref (SOME[]);
    
    fun get_node (id:int) : node = !(Vector.sub(G,id));
    fun set_node ((id:int),(node: node)) = (Vector.sub(G,id)) := node;
    
    fun die (): unit = (result := NONE);
    
    fun find((s_id: int)) : int = let
    val node = get_node s_id;
    val class = get_class node;
    in
    if class = s_id then s_id else let
        val t_id = find class;
        val () = set_node(s_id,node_with_class node t_id);
        in t_id end
    end;
    
    fun union((s_id: int),(t_id: int)) : unit = if not (isSome (!result)) then () else let
    val s_node = get_node s_id;
    val t_node = get_node t_id;
    val new_size = (get_size s_node) + (get_size t_node);
    in if (get_size s_node) >= (get_size t_node) then (
        set_node (s_id,node_with_size_vars_schema_meta s_node new_size (concat_vars(s_node,t_node)) (case get_schema s_node of Var(_) => get_schema t_node | Fun(a,b) => Fun(a,b)) (case get_term_meta_info s_node of Var_(_) => get_term_meta_info t_node | Fun_(a,b) => Fun_(a,b) ));
        set_node (t_id,node_with_class t_node s_id))
    else (
        set_node (t_id,node_with_size_vars_schema_meta t_node new_size (concat_vars(t_node,s_node)) (case get_schema t_node of Var(_) => get_schema s_node | Fun(a,b) => Fun(a,b)) (case get_term_meta_info t_node of Var_(_) => get_term_meta_info s_node | Fun_(a,b) => Fun_(a,b) ));
        set_node (s_id,node_with_class s_node t_id)) end;
    
    fun unif_closure((s_id: int),(t_id: int)) : unit = if not (isSome (!result)) then () else let
        val s_repr_id = find s_id;
        val t_repr_id = find t_id;
        in if s_repr_id=t_repr_id then () else let
            val s_node = get_node s_repr_id;
            val t_node = get_node t_repr_id;
            val s_term_meta_info = get_term_meta_info s_node;
            val t_term_meta_info = get_term_meta_info t_node;
            in case s_term_meta_info 
               of Fun_(s_name,s_argsIds) => (
                   case t_term_meta_info
                   of Fun_(t_name,t_argsIds) =>
                       if s_name = t_name andalso (length s_argsIds) = (length t_argsIds) then (union(s_repr_id,t_repr_id); ListPair.app unif_closure (s_argsIds,t_argsIds)) else die()
                   |  Var_(_) => union(s_repr_id,t_repr_id))
               |  Var_(_) => union(s_repr_id,t_repr_id)
            end
        end;
        
    fun add_substitution name term = if not (isSome (!result)) then () else let
        val new_substitution = (name,term)::(valOf(!result));
        val () = result := SOME(new_substitution);
        in () end;
    
    fun find_solution((s_id: int)) : unit = if not (isSome (!result)) then () else let
(*         val () = print (concat ["find_solution ",Int.toString s_id,"\n"]); *)
        val s_real_id = find s_id;
        val s_real_node = get_node s_real_id;
        val s_schema = get_schema s_real_node;
        in if get_acyclic s_real_node then () else
        if get_visited s_real_node then die() else (
        case get_term_meta_info s_real_node
        of Var_(_) => ()
        |  Fun_(name,argsIds) => (
            set_node(s_real_id,node_with_visited s_real_node true);
            app find_solution argsIds;
            set_node(s_real_id,s_real_node));
        set_node(s_real_id,node_with_acyclic s_real_node true);
        case get_term_meta_info s_real_node
        of Var_(name) => let val e_name = explode name in
            for_each_var s_real_node (fn x => if x=e_name then () else add_substitution x s_schema) end
        |  Fun_(_,_) => for_each_var s_real_node (fn x => add_substitution x s_schema) )
    end;
    
    val () = unif_closure(t1id,t2id);
    val () = find_solution(t1id);
    in !result end;

    
end; (* local *)