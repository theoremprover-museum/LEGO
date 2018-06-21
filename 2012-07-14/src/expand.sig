(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* 
   $Log: type-sig.sml,v $
   Revision 1.2  1997/11/24 11:02:05  tms
   merged immed-may-fail with main branch

   Revision 1.1.2.2  1997/10/13 16:21:44  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.

   Revision 1.1.2.1  1997/10/10 17:02:49  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.1  1997/05/08 13:59:20  tms
   Generalised Expansion Mechanism to Cope with Path information
*)


signature EXPAND =
    sig

   	type cnstr (* = Term.cnstr *)
(* 
   	val expand : string -> cnstr -> cnstr
     (* expand s c expands all Ref occurrences named s in c *)
   
	val expAll : int -> cnstr -> cnstr
     (* expAll 0 c       = c
        expAll (suc n) c expands all definitions in (expAll n c) *)
 *)
     (* ****************************************************************** *
        val subtermApp : int list -> (cnstr -> cnstr) -> cnstr -> cnstr
     (* subtermApp p f c uses f to translate a subterm of c. The subterm
        is characterised by the path p; see the module pbp for further 
        details *)
      * ****************************************************************** *)

	val Expand    : int list -> string list -> cnstr -> cnstr
	val ExpandAll : int list ->     int     -> cnstr -> cnstr

    end
        	
