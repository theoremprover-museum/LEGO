(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* 
   $Log: tactics-sig.sml,v $
   Revision 1.4  1997/11/24 11:01:57  tms
   merged immed-may-fail with main branch

   Revision 1.3.2.3  1997/10/13 16:47:20  djs
   More problems with the above.

   Revision 1.3.2.2  1997/10/13 16:21:40  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.3.2.1  1997/10/10 17:02:47  djs
   Made everything work on Solaris, by taking out some nested comments.
  
    Revision 1.3  1997/05/08 13:42:47  tms
   added support for adding tactics
*)

signature TACTICS =
    sig
	type cnstr_c

 	type tactic		
	val mkTactic : (unit -> unit) -> tactic
	val execute  : tactic -> unit

(* 2011: moved to Toplevel *)
(*
        val Assumption : int -> unit
	val Immed : (int * string) list -> unit
 *)
(* 2011: moved to Logic

	val ExElim : int -> cnstr_c -> unit
	val ExIntro : int -> cnstr_c -> unit
	val AndElim : int -> cnstr_c -> unit
	val AndIntro : int -> unit
	val OrElim : int -> cnstr_c -> unit
	val OrIntroL : int -> unit
	val OrIntroR : int -> unit
	val NotElim : int -> cnstr_c -> unit
	val NotIntro : int -> unit
	val AllIntro : int -> unit
	val AllElim : int -> cnstr_c -> unit
 *)
	val Config_Qrepl : string * string * string -> unit (* semantics changed 2011 *)
	val Qreplace : int -> cnstr_c -> unit

	(* ** Domain-specific tacticals added by users ** *)

	(* * add_tactic id f adds tactical f with name id *

	 * This can then be invoked via UTac id        	  *)
	val init_tactics : unit -> unit
	val add_tactic : string -> (unit -> unit) -> unit
	val ExecUserTac : string -> unit
	val remove_tactic : string -> unit
    end;
