(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* 2011: separated out *)
signature SUBST = 
   sig

	type cnstr 
	type binding 

	type assignment (* = int * cnstr *)
	type substitution (* = assignment list *) 

	val nilS : substitution

	val unSubst  : substitution -> (int * cnstr) list (* !!! *)

	val mkAssign : int * cnstr -> assignment (* !!! *)
	val mkSubst1 : int * cnstr -> substitution (* !!! *)

	val subst1 : cnstr -> cnstr -> cnstr
	val subst1closed : cnstr -> cnstr -> cnstr

(* 2011: adapted from expand/discharge *)

	val expandRef_as_needed : (binding -> bool) -> cnstr -> cnstr

(* 2011: moved from Namespace *)
(* for discharge and for implementation of Cut: refactor!!! *)
        val sub_Ref_pr 	: substitution -> cnstr * cnstr -> (cnstr * cnstr) Utils.Modif.modif
	val subRef     	: substitution -> cnstr -> cnstr
	val subRef_pr  	: substitution -> cnstr * cnstr -> cnstr * cnstr 
	

	val dom		: int -> substitution -> bool 

	val sub		: substitution -> cnstr -> cnstr
    	val sub_pr 	: substitution -> cnstr * cnstr -> cnstr * cnstr
    	val compose 	: (substitution->cnstr->cnstr) -> 
    		  	   substitution -> substitution -> substitution
(* common cases *)
	val composeSub1    : assignment -> substitution -> substitution
	val composeSubRef1 : assignment -> substitution -> substitution
   end
