(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature ABST = 
sig

(* 2011: adapted from subst2 *)
(* Substitute Rel(1) for subterms satisfying predicate P *)

   	type cnstr 

	val abst : (cnstr -> bool) -> cnstr -> cnstr

end
