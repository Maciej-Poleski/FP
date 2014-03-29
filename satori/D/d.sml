fun dfs L =
    let
        val G = Vector.fromList(L);
        val V = Array.array(Vector.length G, false);
        val R = ref [];
        fun impl v =
            if Array.sub(V,v) then
                ()
            else
                let
                    val () = Array.update(V, v, true);
                    val () = R := (v :: !R);
                in
                    app (fn u => impl u) (Vector.sub(G,v))
                end
        val () = Vector.appi (fn (i, _) => impl i) G;
    in
        rev (!R)
    end
