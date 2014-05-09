functor TYPECHECK(U:UNIFIER) = struct
        datatype ttype = VAR_ of label
                        | GENERIC_ of label
                        | ARR_ of ttype * ttype
                        | LIST_ of ttype
                        | INT_;
        val instance_count = ref 0;
        
        fun make_new_instance_name l = let
            val result = concat [l,Int.toString (!instance_count)];
            val () = instance_count := (!instance_count)+1;
            in result end;
        
        fun instantiate ((INT_): ttype) : TTerm = INT
        |   instantiate (VAR_ l) = VAR l
        |   instantiate (GENERIC_ l) = VAR (make_new_instance_name l)
        |   instantiate (ARR_ (a,b)) = ARR (instantiate a, instantiate b)
        |   instantiate (LIST_ (a)) = LIST (instantiate a);

        fun find_label_instance (l:label) [] = NONE
        |   find_label_instance l ((name,term)::rest) = if name=l then SOME (instantiate term) else find_label_instance l rest;

        fun impl (Number _) context = SOME INT
        |   impl (Label label) context = find_label_instance label context;
        
        local
            fun parse_TTerm ((VAR label): TTerm) : ttype = GENERIC_ label
            |   parse_TTerm (ARR (a,b)) = ARR_ (parse_TTerm a, parse_TTerm b)
            |   parse_TTerm (LIST a) = LIST_ (parse_TTerm a)
            |   parse_TTerm (INT) = INT_;
        in
            fun parse_context (context: (string * TTerm) list): (string * ttype) list = map (fn (a,b) => (a,parse_TTerm b)) context;
        end;

        fun typecheck lmterm context = impl lmterm (parse_context context);
end
