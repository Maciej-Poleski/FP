fun max_cycle_length V = 
    let
        val visited = Array.array (length V, 0);
        val Vv = Vector.fromList V;
        fun visit i size =
            if Array.sub (visited, i) = 1 then
                size
            else
                let
                    val () = Array.update (visited, i, 1)
                in visit (Vector.sub (Vv, i)) (size+1) end
    in foldl (fn (i,max) => let val c = visit i 0 in if c > max then c else max end) 1 V end;
    
fun printA arr= Array.foldl (fn (x,_) => print (Int.toString x ^":")) () arr;

fun sort arr =
    Array.foldli (fn (i, c, ()) => let
                                val selected = Array.foldli (fn (j, v, best) => if (j>= i) andalso (v < Array.sub(arr, best)) then j else best) i arr;
                                val tmp = Array.sub(arr,selected);
                                val () = Array.update(arr,i,tmp);
                                val () = Array.update(arr,selected,c);
                            in () end) () arr;
                            
datatype 'a Tree = Empty | Two of 'a Tree * 'a * 'a Tree;

fun insert cmp x Empty= Two (Empty,x,Empty)
        |insert cmp x (Two (l,y,r))= if (cmp (x,y)<0) then Two (insert cmp x l, y, r)
                else Two (l,y,insert cmp x r); 

fun fromList cmp xs= foldl (fn (x,tr) => insert cmp x tr) Empty xs

fun mcmp (x,y) = x-y;

val tr1= fromList mcmp [6,5,4,1,9,3,5];

fun bfs start =
    let
        fun impl nodes =
            foldl (fn (Empty, result) => result
                    | (Two (left, v, right), (nextLayer, values)) => (nextLayer @ [left,right], values @ [v])
            ) ([],[]) nodes;
        fun execute result [] = result
        |   execute result nodes =
            let val (newNodes, results) = impl nodes
            in execute (result @ results) newNodes end
        in
            execute [] [start]
    end

