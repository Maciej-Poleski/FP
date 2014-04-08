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
                                                                                                                                  |  GREATER => lookup (key, right)))
        fun insert (entry,  tree) = ()
end;
