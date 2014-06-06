module F1 where 

--inc = (\n ->  (n+1))

inc n = (+) 1 n	-- definicja funkcji inc 

par n = (mod n 2) == 0 	-- uwaga na różne równości i kolejność wiązania

cK x y = x	-- kombinator K 
{- 
nie musimy nazywać argumentów, których nie używamy, cK możemy równie dobrze zdefiniować jako 
	cK x _ = x
-}

dpow n = (^) n n 


perim r = let 
		pi= 3.14
	in 2* pi * r

cArea n= let 
		pi= 3.14
		n2= n*n
	in pi * n2

