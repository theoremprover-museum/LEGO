(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature TACTICALS =
    sig
	type tactic (* = unit -> unit (* sharing with {Tactics,ConorThen}.tactic *) *)

	val tactical_else : tactic -> tactic -> tactic
	val tactical_null : tactic
	val tactical_fail : tactic
	val tactical_succeed : tactic
	val tactical_try : tactic -> tactic
	val tactical_repeat : tactic -> tactic
	val tactical_for : int -> tactic -> tactic
    end;
