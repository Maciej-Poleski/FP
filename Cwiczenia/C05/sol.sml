signature QUEUE2= sig
	type elT
	type queue

	exception Empty
	val empty: queue
	val enqueue:elT * queue ->  queue
	val dequeue:queue -> elT * queue
end;

structure IQueue:QUEUE2 = struct
    type elT = int
    type queue = elT list
    
    exception Empty
    
    val empty = []
    
    fun enqueue (a,q) = a::q
    
    fun dequeue [] = raise Empty
    |   dequeue [a] = (a,[])
    |   dequeue (x::xs) = let val (a, b) = dequeue xs in (a, x::b) end

end;

signature COMPARABLE= sig
        type t;
        val cmp: t*t -> order   
end;

structure CInt: COMPARABLE= struct
        type t= int;
        val cmp= Int.compare;
end;


functor OSet(structure Val : COMPARABLE)= struct
        structure Val=Val;
        type oset = Val.t list;

        val empty=[];
        fun insert (x,[]) = [x]|
                insert (x,y::ys)= (case (Val.cmp (x,y)) of
                        LESS    =>      x::(y::ys) |
                        EQUAL   =>  y::ys |
                        GREATER => y::(insert (x,ys)) 
                        );

        fun member (x,[]) = false|
                member (x,y::ys)= (case (Val.cmp (x,y)) of
                        LESS    =>      false |
                        EQUAL   =>  true |
                        GREATER => member (x,ys)
                        );
end;

signature DICT= sig
        structure Key:COMPARABLE;

        type 'vt dict;

        val empty: 'vt dict;
        val insert: (Key.t * 'vt) * 'vt dict -> 'vt dict
        val lookup: (Key.t * 'vt dict) -> 'vt option            
end;

signature DICTV= sig
        structure Key:COMPARABLE;
        type vT;        
        type  dict;

        val empty: dict;
        val insert: (Key.t * vT) *  dict -> dict
        val lookup: (Key.t * dict) -> vT option         
end;

functor Dict(structure Key : COMPARABLE) :> DICT = struct
    structure Key=Key
    type 'vt dict = (Key.t * 'vt) list
    
    val empty=[]
    
    fun insert ((k,v),[]) = [(k,v)]
    |   insert ((k,v),(kx,vx)::xs) = (case Key.cmp (k,kx) of
                                          LESS => (k,v)::(kx,vx)::xs
                                        | EQUAL => (kx,vx)::xs
                                        | GREATER => (kx,vx)::(insert ((k,v),xs))
                                     )
    fun lookup (k,[]) = NONE
    |   lookup (x,(k,v)::rest) = (case Key.cmp (x,k) of
                                    LESS => NONE
                                  | EQUAL => SOME v
                                  | GREATER => lookup (x,rest)
                                 )
end;

functor Dictv(structure Key : COMPARABLE type Value) :> DICTV = struct
    structure Key=Key
    type vT = Value
    type dict = (Key.t * vT) list
    
    val empty=[]
    
    fun insert ((k,v),[]) = [(k,v)]
    |   insert ((k,v),(kx,vx)::xs) = (case Key.cmp (k,kx) of
                                          LESS => (k,v)::(kx,vx)::xs
                                        | EQUAL => (kx,vx)::xs
                                        | GREATER => (kx,vx)::(insert ((k,v),xs))
                                     )
    fun lookup (k,[]) = NONE
    |   lookup (x,(k,v)::rest) = (case Key.cmp (x,k) of
                                    LESS => NONE
                                  | EQUAL => SOME v
                                  | GREATER => lookup (x,rest)
                                 )
end;