(*datatype 'a node = Two of 'a node * 'a * 'a node |
                 Three of 'a node * 'a * 'a node * 'a * 'a node |
                 Empty; *)
                 
local
    datatype 'a result = Single of 'a node (* węzeł *)
    |                    Double of 'a * 'a node * 'a node; (* wartość, lewy, prawy *)
    
    fun impl cmp (x, (Empty)) = Single (Two (Empty, x, Empty))
    |   impl cmp (x, (Two (Empty, y, Empty))) =
            if (cmp (x,y)) < 0 then
                Single (Three (Empty, x, Empty, y, Empty))
            else
                Single (Three (Empty, y, Empty, x, Empty))
    |   impl cmp (x, (Three (Empty, y, Empty, z, Empty))) =
            if (cmp (x,y)) < 0 then
                Double (y, Two (Empty, x, Empty), Two (Empty, z, Empty))
            else if (cmp (x,z)) < 0 then
                Double (x, Two (Empty, y, Empty), Two (Empty, z ,Empty))
            else
                Double (z, Two (Empty, y, Empty), Two (Empty, x, Empty))
    |   impl cmp (x, (Two (left, y, right))) =
            if (cmp (x,y)) < 0 then
                case impl cmp (x, left) of Single (n) => Single (Two (n, y, right))
                |                          Double (n, l, r) => Single (Three (l, n, r, y, right))
            else
                (case impl cmp (x, right) of Single (n) => Single (Two (left, y, n))
                |                           Double (n, l, r) => Single (Three (left, y, l, n, r)))
    |   impl cmp (x, (Three (left, y, center, z, right))) =
            if (cmp (x,y)) < 0 then
                case impl cmp (x, left) of Single (n) => Single (Three (n, y, center, z, right))
                |                          Double (n, l, r) => Double (y, Two (l, n, r), Two (center, z, right))
            else if (cmp (x,z)) < 0 then
                case impl cmp (x, center) of Single (n) => Single (Three (left, y, n, z, right))
                |                            Double (n, l, r) => Double (n, Two (left, y, l), Two (r, z, right))
            else
                case impl cmp (x, right) of Single (n) => Single (Three (left, y, center, z, n))
                |                           Double (n, l, r) => Double (z, Two (left, y, center), Two (l, n, r));
in
    fun insert (cmp: ('a * 'a) -> int) ((x: 'a), (T: 'a node)) : 'a node = 
        case impl cmp (x, T) of Single (n) => n
        |                       Double (n, left, right) => Two (left, n, right);
end
