
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
