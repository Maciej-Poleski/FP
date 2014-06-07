module Solution where
import System.Random

newtype Randomised a = Rand (StdGen->(a, StdGen))
instance Monad Randomised where
	Rand(a) >>= f = Rand(\gen -> let
		(na,ngen) = a gen
		in case (f na) of
			Rand(b) -> b ngen)
	Rand(a) >> Rand(b) = Rand(\gen -> b $ snd $ a gen)
	return a = Rand(\gen -> (a,gen))


getNextIdx list = Rand(randomR (0,length list - 1))

solution :: (Ord a) => [a] -> Randomised [a]
solution [] = return []
solution list = do
	idx <- getNextIdx list;
	let
		pivot = list !! idx
		left = filter (\x -> x<pivot) list
		center = filter (\x -> x==pivot) list
		right = filter (\x -> x>pivot) list
		in
		do
			leftR <- solution left;
			rightR <- solution right;
			return $ leftR++center++rightR
