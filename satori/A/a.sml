fun fib n = let fun aux a b 0 : IntInf.int = a
                  | aux a b m = aux b (a+b) (m-1)
	        in aux 0 1 n end;
