module F2 where 

-- import Char

-- om n= om (n+1)
-- om n= om n
-- om = om
om n = 1+ (om n) 

squareSum n= if (n<1) then 0 else (n^2 + squareSum(n-1))

fibb1 n= case n of	
		0 	  -> 1
		1	  -> 1
		otherwise -> (fibb1 (n-1)) + (fibb1 (n-2))

{- jeszcze jeden przykład, żeby było widać, że case nie musi dotyczyć jedynie wartości argumentów -}
par n = case (mod n 2) of
		0 -> True
		1 -> False

{- nic ciekawego ale sie przydaje -}
bToi b= case b of
		True -> 1
		False-> 0



fibb2 n
		|(n==0 || n==1)	= 1
		| n < 0 	= (fibb2 (n+2)) - (fibb2 (n+1))
		| n>1  		= (fibb2 (n-1)) + (fibb2 (n-2))
		| otherwise 	= 1 	-- to można było sobie darować

fibb3  0 = 1
fibb3  1 = 1
fibb3  n = (fibb3 (n-1)) + (fibb3 (n-2))

--  odkomentuj tą funkcję żeby zobaczyć jak nie działa
-- fibb4  n = (fibb4 (n-1)) + (fibb4 (n-2)) 
-- fibb4  0 = 1
-- fibb4  1 = 1



{- dlaczego poniższa funkcja nie kończy działania dla argumentu 4 (na przykład)? popraw ją -}
fac 1 	= 1
fac n	= n * (fac (n-1))

{- zdefiniuj deltę Kroneckera: deltaK a b == 1  wtw a==b -}
deltaK a b 
    | a==b = 1
    | otherwise = 0
    

{- napisz predykat pierwszości (jak najbardziej naiwnie) -}
isPrime a = let
                check a n
                    | n<2 = True
                    | otherwise = case mod a n of
                                       0 -> False
                                       otherwise -> check a (n-1)
            in check a (a-1)


{- napisz funkcję mGCD obliczającą największy wspólny dzielnik-}
mGCD a b
    | b==0 = a
    | otherwise = mGCD b (mod a b)