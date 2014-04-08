(*
datatype 'a node = Two of 'a node * 'a * 'a node |
                 Three of 'a node * 'a * 'a node * 'a * 'a node |
                 Empty;

signature COMPARABLE= sig
        type t;
        val cmp: t*t -> order
end;

signature DICT= sig
        structure Key:COMPARABLE;

        type 'vt dict;

        val empty: 'vt dict;
        val insert: (Key.t * 'vt) * 'vt dict -> 'vt dict;
        val lookup: (Key.t * 'vt dict) -> 'vt option;
end;

signature OSET= sig
        structure Key:COMPARABLE;

        type oset;

        val empty: oset;
        val insert: Key.t * oset -> oset;
        val member: Key.t * oset -> bool;
end;

datatype 'b Propagate= Good of 'b | PropagateUp of 'b;

signature SPEC = sig
        structure Key:COMPARABLE;
        type 'vT entryT;
        type 'vT resultT;


        val extractKey: 'vT entryT -> Key.t;
        val updateE: 'vT entryT node * 'vT entryT -> 'vT entryT node Propagate;
        val lookupE: 'vT entryT option -> 'vT resultT;
end;
*)

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

local
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
in
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
end


(*


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

structure cInt: COMPARABLE= struct
        type t= int;
        val cmp = Int.compare;
end;

structure TD= TDict(structure KeyS=cInt);
structure TS= TSet(structure KeyS=cInt);

*)