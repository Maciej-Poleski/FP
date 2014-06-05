functor Queue (Stacks : STACKS) : RQUEUE =
struct
      open Stacks;
      type 'a stacks = 'a Stacks.stacks;
      datatype 'a info = Info of bool (* rev append active *)
                               * bool (* deq active *)
                               * int (* skip from front *)
                               ;
                               
      fun is_rev_active (Info(a,_,_)) = a;
      fun is_deq_active (Info(_,b,_)) = b;
      fun get_skip (Info(_,_,c)) = c;
      fun inc_skip (Info(a,b,c)) = Info(a,b,c+1);
      fun set_deq_active (Info(a,_,c)) b = Info(a,b,c);
      fun get_for (stacks,state) = size 1 stacks - size 0 stacks + (if is_deq_active state then 1 else 0);
                               
      fun need_activation (stacks,Info(rev,deq,_)) = size 0 stacks - (if deq then 1 else 0) <= size 1 stacks andalso size 1 stacks > 0 andalso ((*if rev then print "Aktywacja przed zakończeniem poprzedniego zadania\n" else ();*) rev = false)
                               
      and execute_trigger (stacks,state) = if need_activation (stacks,state) then let
        val for = get_for (stacks,state);
        val new_state = Info(true,is_deq_active state,0);
        val new_stacks = clear 1 (dup 0 2(dup 1 3 (clear 4 (clear 5 stacks))));
        val result= (new_stacks,new_state);
        in exec3for result for end else (stacks,state)
      and execute_tasks (stacks,state) = if size 3 stacks > 0 then let
        val new_stacks = pop 3 (copy 3 5 stacks);
        in (new_stacks,state) end else if size 2 stacks > 0 then let
        val new_stacks = pop 2 (copy 2 4 stacks);
        in (new_stacks,state) end else if size 4 stacks - get_skip state > 0 then let
        val new_stacks = pop 4 (copy 4 5 stacks);
        in (new_stacks,state) end else (stacks,state)
      and finish_tasks (stacks,state) = if empty 2 stacks andalso empty 3 stacks andalso size 4 stacks = get_skip state andalso is_rev_active state then let
        val new_state = Info(false,is_deq_active state,0);
(*         val () = print ("Przesypuje: "^(String.concatWith " " (map Int.toString (get_stack 5 stacks)))^"\n"); *)
        val new_stacks = dup 5 0 stacks; (*(if is_deq_active state then copy 4 5 stacks else stacks);*)
        in (new_stacks,new_state) end else (stacks,state)
      and exec (stacks,state) = execute_trigger(finish_tasks(execute_tasks(stacks,state)))
      
      and exec2 ss = exec(exec(ss))
      
      and exec3 ss = exec(exec2(ss))
      and exec3for ss 0 = ss
      |   exec3for ss i = exec3for (exec3(ss)) (i-1);
                               
      val qnil = (Stacks.snil, Info(false,false,0));
      fun enq (stosy, stan) = exec3 (pop 0 (copy 0 1 stosy),stan);
      fun deq (stosy, stan) = let
        val new_state=set_deq_active stan true;
        val (stack_r,state_r) = exec3 (stosy,new_state);
        in (stack_r,inc_skip (set_deq_active state_r false)) end;
end

