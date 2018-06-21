(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* cml.sml *)

signature PARTM = 
sig
	type cnstr 
	type substitution 

   exception CML_UNIMPLEMENTED

   val par_tm_debug : bool ref  
   val par_unif_debug : bool ref  

   val par_tm_switch : bool ref 
   val par_unif_switch : bool ref  

   val timeslice : int ref

   val par_tm    : cnstr -> cnstr -> bool

   val par_unif  : substitution -> cnstr -> cnstr -> substitution option 
   val par_unif0 : cnstr -> cnstr -> substitution option 

end


(* ******************************************************** *
   need to add explicit support for CML; 
   guide recommends use of compilation manager CM, groan
   achieved 11-11-2011

 * ******************************************************** *)

functor FunParTm (structure Subst : SUBST 
		  structure UMopen : UMOPEN 
		  structure Unif : UNIF 
		  structure Pretty : PRETTY
		  sharing 
		   	   type Subst.cnstr
			      = UMopen.cnstr
			      = Unif.cnstr
			      = Pretty.cnstr
		  and 
		   	   type Subst.substitution
			      = Unif.substitution
		  ) 
(* *** *
structure ParTm 
 * *** *)
	: PARTM
 = 

struct

	type cnstr = Subst.cnstr (* 2011 *)
	type substitution = Subst.substitution

   exception CML_UNIMPLEMENTED

(* include CML stuff; (* how??? *) *)

val par_tm_debug = ref false;
val par_unif_debug = ref false;

val par_tm_switch = ref true (* previously these branches were inverted *);
val par_unif_switch = ref true;

val timeslice = ref 50;

local

   val prs = Printing.prs
   val message = Printing.message

   val legoprint = Pretty.legoprint

(*  *)

   val nilS	       = Subst.nilS 

   val sameTerm        = UMopen.sameTerm 
   val type_match      = UMopen.UMtype_match

   val type_match_heur = Unif.type_match_heur
   val type_match_unif = Unif.type_match_unif
   val whnf_unif       = Unif.whnf_unif

in

(* code to support parallel (time-sliced) search for conversion tests *)

fun par_tm c d =
  (if (!par_tm_debug) 
      then (message("**par_tm_deb: switch is "^Bool.toString (!par_tm_switch));
	    prs"** "; legoprint c;
	    prs"** "; legoprint d)
   else ();

   if (!par_tm_switch) then UMopen.UMtype_match c d
   else

	raise CML_UNIMPLEMENTED

(* ******************************************************** *
   need to add explicit support for CML; 
 * ******************************************************** *

     let
       val cml_tm_ans = ref false;
       fun cml_tm () =
	 let
	   val chan = CML.channel()
	   fun whnf_tm() = CML.send(chan,sameTerm c d orelse type_match c d)
	   fun heur_tm() = CML.send(chan,type_match_heur c d)
	   val whnf_tid = CML.spawn whnf_tm
	   val heur_tid  = CML.spawn heur_tm
	   val _ = cml_tm_ans:= CML.accept chan
	 in
	   RunCML.shutdown()
	 end
     in
       (RunCML.doit(cml_tm,SOME(!timeslice)); !cml_tm_ans)
     end
 * ******************************************************** *)

     );

fun par_unif s c d =
  (if (!par_unif_debug) 
      then (message("**par_unif_deb: switch is "^Bool.toString (!par_unif_switch));
	    prs"** "; legoprint c;
	    prs"** "; legoprint d)
   else ();

   if (!par_unif_switch) then type_match_unif s c d
   else

	raise CML_UNIMPLEMENTED

(* ******************************************************** *
   need to add explicit support for CML; 
 * ******************************************************** *

     let
       val cml_unif_ans = ref NONE;
       fun cml_unif () =
	 let
	   val chan = CML.channel()
	   fun Whnf_unif() =
	     case whnf_unif s c d 
	       of x as (SOME t) => CML.send(chan,x)
	        | NONE => ()
	   fun heur_unif() = CML.send(chan,type_match_unif s c d)
	   val whnf_tid = CML.spawn Whnf_unif
	   val heur_tid  = CML.spawn heur_unif
	   val _ = cml_unif_ans:= CML.accept chan
	 in
	   RunCML.shutdown()
	 end
     in
       (RunCML.doit(cml_unif,SOME(!timeslice)); !cml_unif_ans)
     end
 * ******************************************************** *)

    );

val par_unif0 = par_unif nilS;

end (* local decl of legoprint *)

end; (* struct *)

(*
val _ = r_par_tm:= par_tm;  * setup foward reference *
 *)


     
