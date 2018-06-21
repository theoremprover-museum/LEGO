(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* toc.sig *)

signature TOC =  
  sig

    type cnstr 

(* ****************************** *
    val kind : cnstr -> bool		(* moved to Namespace *)
    val coerceGe : cnstr -> cnstr	(* moved to Machine *)
 * ****************************** *)

    val TheoryProject : string -> cnstr -> cnstr * cnstr (* changed type *)

    val type_of_constr : cnstr -> cnstr

  end;
