(*datatype 'a node = Two of 'a node * 'a * 'a node |
                 Three of 'a node * 'a * 'a node * 'a * 'a node |
                 Empty; *)

local
    datatype 'a result = Balanced of 'a node (* nie ma potrzeby naprawiania *)
    |                    High of 'a node; (* węzeł jest zbyt wysoko *)
    
    fun fix_left_two (r, (Balanced (a))) b d = (r, Balanced (Two (a, b, d)))
    |   fix_left_two (r, (High (a))) b (Two (c, d, e)) = (r, High (Three (a, b, c, d, e)))
    |   fix_left_two (r, (High (a))) b (Three (c, d, e, f, g)) = (r, Balanced (Two (Two (a, b, c), d, Two (e, f, g))));
    
    fun fix_right_two b d (r, (Balanced e)) = (r, Balanced (Two (b, d, e)))
    |   fix_right_two (Two (a, b, c)) d (r, High e) = (r, High (Three (a, b, c, d, e)))
    |   fix_right_two (Three (a, b, c, d ,e)) f (r, High g) = (r, Balanced (Two (Two (a, b, c), d, Two (e, f, g))));
    
    fun fix_left_three (r, Balanced a) b d f g = (r, Balanced (Three (a, b, d, f, g)))
    |   fix_left_three (r, High a) b (Two (c, d, e)) f g = (r, Balanced (Two (Three (a, b, c, d, e), f, g)))
    |   fix_left_three (r, High a) b (Three (c, d, e, f, g)) h i = (r, Balanced (Three (Two (a, b, c), d, Two (e, f, g), h, i)));
    
    fun fix_center_three a b (r, Balanced c) d f = (r, Balanced (Three (a, b, c, d, f)))
    |   fix_center_three a b (r, High c) d (Two (e, f, g)) = (r, Balanced (Two (a, b, Three (c, d, e, f, g))))
    |   fix_center_three a b (r, High c) d (Three (e, f, g, h, i)) = (r, Balanced (Three (a, b, Two (c, d, e), f, Two (g, h, i))));
    
    fun fix_right_three a b d f (r, Balanced g) = (r, Balanced (Three (a, b, d, f, g)))
    |   fix_right_three a b (Two (c, d, e)) f (r, High g) = (r, Balanced (Two (a, b, Three (c, d, e, f, g))))
    |   fix_right_three a b (Three (c, d, e, f, g)) h (r, High i) = (r, Balanced (Three (a, b, Two (c, d, e), f, Two (g, h, i))));
    
    fun extract_left (Two (Empty, x, Empty)) = (x, High Empty)
    |   extract_left (Three (Empty, x, Empty, y, Empty)) = (x, Balanced (Two (Empty, y, Empty)))
    |   extract_left (Two (left, x, right)) =
            let val (v, r) = extract_left left
            in (v, #2(fix_left_two (true, r) x right)) end
    |   extract_left (Three (left, x, center, y, right)) =
            let val (v, r) = extract_left left
            in (v, #2(fix_left_three (true, r) x center y right)) end;
    
    fun impl cmp (x, (Empty)) = (false, Balanced (Empty))
    |   impl cmp (x, (Two (Empty, y, Empty))) =
            if (cmp (x, y)) < 0 then
                fix_left_two (impl cmp (x, Empty)) y Empty
            else if (cmp (x, y)) > 0 then
                fix_right_two Empty y (impl cmp (x, Empty))
            else
                (true, High (Empty))
    |   impl cmp (x, Three (Empty, y, Empty, z, Empty)) =
            if (cmp (x, y)) < 0 then
                fix_left_three (impl cmp (x, Empty)) y Empty z Empty
            else if (cmp (x, y)) = 0 then
                (true, Balanced (Two (Empty, z, Empty)))
            else if (cmp (x, z)) < 0 then
                fix_center_three Empty y (impl cmp (x, Empty)) z Empty
            else if (cmp (x, z)) = 0 then
                (true, Balanced (Two (Empty, y, Empty)))
            else
                fix_right_three Empty y Empty z (impl cmp (x, Empty))
    |   impl cmp (x, Two (left, y, right)) =
            if (cmp (x, y)) < 0 then
                fix_left_two (impl cmp (x, left)) y right
            else if (cmp (x, y)) = 0 then
                let val (v, r) = extract_left right
                in fix_right_two left v (true, r) end
            else
                fix_right_two left y (impl cmp (x, right))
    |   impl cmp (x, Three (left, y, center, z, right)) =
            if (cmp (x, y)) < 0 then
                fix_left_three (impl cmp (x, left)) y center z right
            else if (cmp (x, y)) = 0 then
                let val (v, r) = extract_left center
                in fix_center_three left v (true, r) z right end
            else if (cmp (x, z)) < 0 then
                fix_center_three left y (impl cmp (x, center)) z right
            else if (cmp (x, z)) = 0 then
                let val (v, r) = extract_left right
                in fix_right_three left y center v (true, r) end
            else
                fix_right_three left y center z (impl cmp (x, right));        
in
    fun remove (cmp: ('a * 'a) -> int) ((x: 'a), (T: 'a node)) : bool * 'a node = 
        case impl cmp (x, T) of (r, Balanced (n)) => (r, n)
        |                       (r, High (n)) => (r, n); (* Drzewo zmniejsza wysokość *)
end
