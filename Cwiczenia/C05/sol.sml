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