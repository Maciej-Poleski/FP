functor Queue (Stacks : STACKS) : RQUEUE =
struct
      open Stacks;
      type 'a stacks = 'a Stacks.stacks;
      datatype 'a info = Info of int (* front size *)
                               * int (* rear size *)
                               * int (* f copy size *)
                               * int (* r copy size *)
                               * int (* f' to copy size *)
                               * int (* r' size *)
                               ;
                               
      fun increase_rear_size (Info(f,r,fc,rc,fp,rs)) = Info(f,r+1,fc,rc,fp,rs);
      fun decrease_front_size (Info(f,r,fc,rc,fp,rs)) = Info(f-1,r,fc,rc,fp-1,rs);
      fun get_for (Info(f,r,_,_,_,_)) = r-f;
      fun get_front (Info(f,_,_,_,_,_)) = f;
      fun get_rear (Info(_,r,_,_,_,_)) = r;
      fun get_front_c (Info(_,_,fc,_,_,_)) = fc;
      fun get_rear_c (Info(_,_,_,rc,_,_)) = rc;
      fun set_front_c (Info(f,p,_,rc,fps,rps)) fc = Info(f,p,fc,rc,fps,rps);
      fun set_rear_c (Info(f,p,fc,_,fp,rs)) rc = Info(f,p,fc,rc,fp,rs);
      fun inc_rear_ps (Info(f,p,fc,rc,fp,rs)) = Info(f,p,fc,rc,fp,rs+1);
      fun get_front_pc (Info(_,_,_,_,fpc,_)) = fpc;
      fun set_front_pc (Info(a,b,c,d,_,f)) fpc = Info(a,b,c,d,fpc,f);
      fun install_new_front (Info(f,r,fc,rc,fpc,rs)) = Info(rs,r,0,0,~1,0);
                               
      fun is_trigger_state (Info(fs,rs,_,_,_,_)) = ((fs <= rs) andalso (rs > 0))
                               
      and execute_trigger (stacks,state) = if is_trigger_state state then let
        val for = get_for state;
        val new_state = Info(get_front state,0,get_front state,get_rear state,get_front state,0);
        val new_stacks = clear 1 (dup 0 2(dup 1 3 (clear 4 (clear 5 stacks))));
        val result= (new_stacks,new_state);
        in exec4for result for end else (stacks,state)
      and execute_tasks (stacks,state) = if get_rear_c state > 0 then let
        val count = get_rear_c state;
        val new_state1 = set_rear_c state (count-1);
        val new_state2 = inc_rear_ps new_state1;
        val new_stacks = pop 3 (copy 3 5 stacks);
        in (new_stacks,new_state2) end else if get_front_c state > 0 then let
        val count = get_front_c state;
        val new_state1 = set_front_c state (count-1);
        val new_stacks = pop 2 (copy 2 4 stacks);
        in (new_stacks,new_state1) end else if get_front_pc state > 0 then let
        val count = get_front_pc state;
        val new_state1 = set_front_pc state (count-1);
        val new_state2 = inc_rear_ps new_state1;
        val new_stacks = pop 4 (copy 4 5 stacks);
        in (new_stacks,new_state2) end else (stacks,state)
      and finish_tasks (stacks,state) = if get_rear_c state = 0 andalso get_front_c state = 0 andalso get_front_pc state = 0 then let
        val new_state = install_new_front state;
(*         val () = print ("Przesypuje: "^(String.concatWith " " (map Int.toString (get_stack 5 stacks)))^"\n"); *)
        val new_stacks = dup 5 0 stacks;
        in (new_stacks,new_state) end else (stacks,state)
      and exec (stacks,state) = execute_trigger(finish_tasks(execute_tasks(stacks,state)))
      
      and exec3 ss = exec(exec(exec(ss)))
      
      and exec4 ss = exec(exec3(ss))
      and exec4for ss 0 = ss
      |   exec4for ss i = exec4for (exec4(ss)) (i-1);
                               
      val qnil = (Stacks.snil, Info(0,0,0,0,~1,0));
      fun enq (stosy, stan) = exec4 (pop 0 (copy 0 1 stosy),increase_rear_size(stan));
      fun deq (stosy, stan) = let
        val (stack_r,state_r) = exec3 (stosy,stan);
        in (stack_r,decrease_front_size state_r) end;
end

