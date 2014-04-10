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

