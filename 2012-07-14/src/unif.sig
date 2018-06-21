(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature UNIF = 
  sig

    type cnstr 
    type assignment (* = int * cnstr  *) 
    type substitution (* = assignment list *)

    val type_match_unif : substitution -> cnstr -> cnstr -> substitution option
    val whnf_unif 	: substitution -> cnstr -> cnstr -> substitution option

    val type_match_unif0 : cnstr -> cnstr -> substitution option
    val type_match_heur  : cnstr -> cnstr -> bool

  end 
