(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

functor FunAbst (structure Term:TERM
		 structure UMopen : UMOPEN
		 structure Pretty : PRETTY
		 sharing 
		   	   type Term.cnstr
			      = UMopen.cnstr
			      = Pretty.cnstr
		  ) 
(* *** * 
structure Abst
 * *** *)
	: ABST 
 = 

struct

local 

      val legoprint = Pretty.legoprint 

      open Utils.Modif  
      open Term 

      val failwith = Utils.Except.failwith 

in

   	type cnstr = Term.cnstr 

fun abst P = 
  let fun abstrec k c = 
      if P c then Mod (Rel k) 
      else case c 
      	     of (App b)   => mkApp (abstrec k) b
     	      | (Bind b)  => mkBind abstrec k b
     	      | (Tuple b) => mkTuple (abstrec k) b
     	      | (CnLst b) => mkCnLst (abstrec k) b
     	      | (Proj b)  => mkProj (abstrec k) b
     	      | (RedTyp b)=> mkRedTyp (abstrec k) b
     	      | (LabVT b) => mkLabVT (abstrec k) b
     	      | _         => UMod
  in 
     share (abstrec 1) 
  end

(* 
fun subst2 bref = 
    let
	val P = fn Ref br   => sameRef br bref 
	      	 | Var(n,t) => if depends bref t
		      	       	  then failwith("type of metavar "
			       	    	      	^Int.toString n
				    	      	^" not closed: "; 
						legoprint t)
		    	       else false
		 | _ => false
    in 
       abst P 
    end
 *)
(* 
fun make_pattern c = abst (UMopen.UMtype_match c)
 *)

end; (* local open Utils, Term *)

end

