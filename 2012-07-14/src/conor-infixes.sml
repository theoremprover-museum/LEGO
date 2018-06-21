(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

structure ConorInfix 

 = 

struct

	infix <- (* assignment to a binder, checking it's a Dom or Voo *)
	infix <: (* update binder_data *)
	infix <! (* update kind *)
	infix :! (* new ref with given binder_data and kind *)
	infix ?!
	infix ?? (* wrap with a context *)
	infix !? (* wrap with the context from a state *)
	infix >> (* voorewrite *)
	infix >>> (* voorewrite state *)
	infix %>>
	infix %>>>
	infix $>>
	infix $>>>
	infix \ (* vooSolve *)

end; 

structure ConorInfixTest

 = 

struct

local 
      val bug = Utils.Except.bug

      open Term

	infix <- (* assignment to a binder, checking it's a Dom or Voo *)
	infix <: (* update binder_data *)
	infix <! (* update kind *)
	infix :! (* new ref with given binder_data and kind *)
	infix ?!
	infix ?? (* wrap with a context *)
	infix !? (* wrap with the context from a state *)
	infix >> (* voorewrite *)
	infix >>> (* voorewrite state *)
	infix %>>
	infix %>>>
	infix $>>
	infix $>>>
	infix \ (* vooSolve *)

in 

fun (B:binding) <- (b:binding) = case ref_kind B
               of _ => bug "Bad Ass Mother!"

end

end;
