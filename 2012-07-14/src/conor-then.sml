(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature CONORTHEN =
sig
  type tactic (* = unit -> unit (* sharing with {Tactics,Tacticals}.tactic *)  *)
  val InitConorThen : unit -> unit
  val RunLazyTactics : unit -> unit
  val Then : tactic -> tactic -> tactic
end

signature CONORTHENSIG = 
sig 
	structure PromptKnots : (* CONORKNOTS *) sig 
				include CONORKNOTS 
				where KT = PromptKnotTypes 
			       end 
	structure UndoKnots   : (* CONORKNOTS *) sig  
				include CONORKNOTS  
				where KT = UndoKnotTypes    
			       end 
end

functor FunConorThen(structure Namespace:NAMESPACE
	             structure CTS:CONORTHENSIG) : CONORTHEN =
struct

  type tactic = unit -> unit

  val message = Printing.message 

  local
    structure GoalKnotTypes:CONORKNOTTYPES =
      struct
        type knot  = int
        type entry = unit -> unit (* Tactics.tactic *)

	fun doIt f = f () (* Tactics.execute *)

	fun isIt (k:knot) = fn g => g=k
      end

    structure GoalKnots = FunConorKnots(GoalKnotTypes)

    fun handle_knot () =
	if Namespace.activeProofState()
	    then let
		     val g = Namespace.current_goal_index ()

(*		     val tac = GoalKnots.seek_one_knot (fn k => k=g)
		     val _ = GoalKnots.remove_all_knots (fn k => k=g)
 *)
		     val tac = GoalKnots.seek_first_knot g
		 in
                     (message "executing delayed Then tactic...");
		     (tac ());
		     (handle_knot ())
		 end
	     handle GoalKnots.no_such_knot => ()
	else GoalKnots.init_knots() (* GoalKnots.remove_all_knots (fn _ => true) *)
  in

    val RunLazyTactics = handle_knot

    fun InitConorThen () =
	( (CTS.PromptKnots.tie_knot RunLazyTactics "ConorThen");
	  (CTS.UndoKnots.tie_knot
	   (fn _ => GoalKnots.init_knots()) 
	       (* fn _ => GoalKnots.remove_all_knots (fn _ => true) *)
	   "Init");
	  (CTS.UndoKnots.tie_knot
	   (fn _ => GoalKnots.push_knots ())
	   "Mark");
	  (CTS.UndoKnots.tie_knot
	   (fn _ => GoalKnots.undo_knots 1)
	   "Undo");
	  (CTS.UndoKnots.tie_knot
	   (fn _ => GoalKnots.discard_knots 1)
	   "Discard") )

    fun Then tac1 tac2 _ =
	let
            val oldNUN = Namespace.getNUN()
	    val old_subgoals = Namespace.current_goal_indexes ()
	    val old_subgoal = hd old_subgoals
	    (* val _ = prs "oldNUN=";pri oldNUN;prs"; old_subgoal=";pri old_subgoal *)
	    val _ = tac1 ()
	in
	    if Namespace.activeProofState() then
		let (* we may need to do the second tac *)
                    val next_subgoals = Namespace.current_goal_indexes ()
		    val next_subgoal = hd next_subgoals
		    val then_list =
			if (next_subgoal>=oldNUN)
                        then Utils.ListUtil.diff next_subgoals old_subgoals
			else if (next_subgoal=old_subgoal) then [old_subgoal]
			     else []
		in
		    ((*(map (fn i:int => ((print i);print " "))
		      then_list);
		     (message " being added");*)
		     (List.map (chain_new_tac tac2) then_list);())
		end
	    else () (* goal already proven *)
	end

    and chain_new_tac t2 g =
	let
(* 	    val t1 = GoalKnots.seek_one_knot (fn k => k=g)
	    val _ = GoalKnots.remove_all_knots (fn k => k=g)
 *)
	    val t1 = GoalKnots.seek_first_knot g
	in
	    GoalKnots.tie_knot (Namespace.no_history (Then t1 t2)) g
	end
        handle GoalKnots.no_such_knot =>
	    GoalKnots.tie_knot (Namespace.no_history t2) g


  end (* local *)
end (* struct *)
