type name = char list;
datatype term = Fun of name * term list | Var of name;

type substitution = (name * term) list;
