module Solution where
data Term= App String [Term] | Var String  deriving (Read)
solution::Term->ShowS
solution (Var n) = showString n
solution (App n []) = showString n
solution (App n list) = showString n . showString "(" . foldl1 (\a b -> a . showString "," . b) (map solution list) . showString ")"
