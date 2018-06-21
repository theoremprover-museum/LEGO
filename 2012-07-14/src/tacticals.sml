(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* tactical.sml
   Thomas Schreiber <lego@dcs.ed.ac.uk>
   January 1995
   Primitive LCF tacticals *)

(* Updated by Conor McBride *)

(* We assume that a tactic which succeeds leaves one history mark, then *)
(* changes the state and returns (). We assume that a tactic which      *)
(* fails makes no history mark, does not change the state and raises an *)
(* exception.                                                           *)

functor FunTacticals (structure Namespace:NAMESPACE
		      structure ConorThen:CONORTHEN
(* 		      structure Tactics:TACTICS
		      sharing 
		      	      type ConorThen.tactic
			      	 = Tactics.tactic
 *)		      ) : TACTICALS =
    struct

	type tactic = unit -> unit  

	exception Failure = Utils.Except.Failure  

	val failwith = Utils.Except.failwith 

	val message = Printing.message 

	fun tactical_null a = a

	local
	    fun do_else t1 t2 () =
		( (Namespace.tacticalPushHist());
                  (Namespace.no_history t1 ());
                  (if (Namespace.activeProofState()) orelse
		      (Namespace.provenState())
		       then Namespace.discard()
		   else ()) )
		handle _ =>
		    ( (message "backtracking...");
		      (if (Namespace.activeProofState()) orelse
		          (Namespace.provenState())
			    then Namespace.undo()
		       else () );
                      (Namespace.no_history t2 ()) )
	in
	    fun tactical_else t1 t2 _ = 
		if Namespace.activeProofState()
		    then Namespace.tactic_wrapper (do_else t1 t2) ()
		else (t1() handle Failure mesg => (* how might they fail? Solve? *)
		      (message mesg;
		       message "No backtracking possible";
		       t2()))
        end

	fun tactical_fail _ = failwith "tactical_fail failed"

	fun tactical_succeed _ = (if Namespace.activeProofState()
			      then Namespace.pushHist()
			  else ())

	fun tactical_try tactical = tactical_else tactical tactical_succeed

	fun tactical_repeat tactical = tactical_else 
	   (fn _ => ((tactical()); 
	       	     (ConorThen.RunLazyTactics());
                      tactical_repeat tactical ()))
           tactical_succeed
	
	fun tactical_for n tactical _ = Utils.FunUtil.repeat n
    	   (fn _ => ( (tactical()); (ConorThen.RunLazyTactics()))) () 
end


