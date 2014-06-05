structure X = Queue(SixStacks);
open X;
fun pre_enq ((cnt, head)::stacks_rest, info) v = ((cnt+1, v::head)::stacks_rest, info);
fun post_deq ((cnt, head::tail)::stacks_rest, info) = (head, ((cnt-1, tail)::stacks_rest, info));
val q = qnil;

local
    val next = ref 0;
    in
    fun get_next () = let
        val result = !next;
        val () = next := result+1;
        in result end;
end

val q = enq (pre_enq q (get_next ()));
val q = enq (pre_enq q (get_next ()));
val q = enq (pre_enq q (get_next ()));
val q = enq (pre_enq q (get_next ()));
val q = enq (pre_enq q (get_next ()));
val (res, q) = post_deq (deq q);
val (res, q) = post_deq (deq q);
val q = enq (pre_enq q (get_next ()));
val q = enq (pre_enq q (get_next ()));
val q = enq (pre_enq q (get_next ()));
val (res, q) = post_deq (deq q);
val (res, q) = post_deq (deq q);
val (res, q) = post_deq (deq q);
val q = enq (pre_enq q (get_next ()));
val q = enq (pre_enq q (get_next ()));
val q = enq (pre_enq q (get_next ()));
val q = enq (pre_enq q (get_next ()));
val (res, q) = post_deq (deq q);
val (res, q) = post_deq (deq q);
val (res, q) = post_deq (deq q);
val (res, q) = post_deq (deq q);
val (res, q) = post_deq (deq q);
val (res, q) = post_deq (deq q);
val (res, q) = post_deq (deq q);