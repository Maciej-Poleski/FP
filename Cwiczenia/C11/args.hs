{-
	Program używa konstrukcji o których nie mówiliśmy ["do", "<-", "return"]. Proszę się na razie na tym nie skupiać. Chodzi tylko o to żebyśmy w linii 11 mogli wstawić dowolną funkcję która zależy od argumentów programu.
-}

module Main where

import System.Environment

main= do 
	args <- getArgs		-- args jest teraz listą argumentów typu String
	putStrLn (show ((read (head args)) + 2))	-- show zamienia dane na ich reprezentacje typu String
	return ()		

{- Ostatnia linia nie jest potrzebna w tym programie.
Jeśli jednak bedziecie go zmieniać, to może sie okazać konieczna.
Nie zastanawiajmy się na razie dlaczego. -}
