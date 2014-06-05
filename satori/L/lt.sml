structure X = Queue(SixStacks);
open X;
fun pre_enq ((cnt, head)::stacks_rest, info) v = ((cnt+1, v::head)::stacks_rest, info);
fun post_deq ((cnt, head::tail)::stacks_rest, info) = (head, ((cnt-1, tail)::stacks_rest, info));
val q = qnil;
