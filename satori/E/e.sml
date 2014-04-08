(*datatype 'a Tree = Leaf | Branch of 'a Tree * 'a * 'a Tree*)

local
    structure Queue = struct
        type 'a queue = 'a list * 'a list;
        
        val empty : 'a queue =([],[]);
        
        fun isEmpty (([],[]): 'a queue) = true
        |   isEmpty _ = false;
        
        fun enqueue (x: 'a) ((a,b): 'a queue) : 'a queue = (x::a,b);
        
        fun dequeue ((a,[]): 'a queue) : 'a * 'a queue = dequeue ([], rev a)
        |   dequeue (a,b::bs) = (b,(a,bs));
    end;
    fun impl (n:int, Q: 'a Tree Queue.queue) : ('a * int) Tree Queue.queue =
        if Queue.isEmpty Q then
            Queue.empty
        else
            let
                val (v,Q) = Queue.dequeue Q;
            in
                case v of Leaf => Queue.enqueue Leaf (impl (n,Q))
                |         Branch (left, label, right) =>
                            let
                                val resultQ = impl (n+1,Queue.enqueue right (Queue.enqueue left Q));
                                val (r,q1) = Queue.dequeue resultQ;
                                val (l,q2) = Queue.dequeue q1;
                            in
                                Queue.enqueue (Branch (l,(label,n),r)) q2
                            end
            end;
in
    fun bfnum (Leaf: 'a Tree) : ('a * int) Tree = Leaf
    |   bfnum (T: 'a Tree) : ('a * int) Tree = #1 (Queue.dequeue (impl (0, Queue.enqueue T Queue.empty)))
end;
