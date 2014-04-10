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

structure cInt3: COMPARABLE= struct
	type t= int*int*int;
	fun cmp ((x1,y1,_), (x2,y2,_)) = (case Int.compare (x1,x2) of
		LESS	=>	LESS|
		GREATER =>	GREATER|
		EQUAL	=> Int.compare (y1,y2)
		);
end;

structure cInt: COMPARABLE= struct
	type t= int;
	val cmp= Int.compare;
end;

structure TS= TSet(structure KeyS=cInt);
structure TD= TDict(structure KeyS=cInt);

val t1= TS.insert (7, TS.empty);
val d1= TD.insert ((7,"a"), TD.empty);
