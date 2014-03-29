fun dfs L =
    let
        val G = Vector.fromList(L);
        val V = Array.array(Vector.length G, false);
        fun impl v =
            if Array.sub(V,v) then
                []
            else
                let
                    val () = Array.update(V, v, true);
                in
                    v :: List.concat (map (fn u => impl u) (Vector.sub(G,v)))
                end
    in
        Vector.foldr (fn (v, r) => v @ r) [] (Vector.mapi (fn (i, _) => impl i) G)
    end
