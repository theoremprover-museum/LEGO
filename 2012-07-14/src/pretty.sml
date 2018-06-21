(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* pretty.sml    un programme d'impression             *)
(* Author         : Randy Pollack                      *)
(* Modified by    : Dilip Sequeira, Randy Pollack & Thomas Kleymann  *)

(* 17 Nov 1996 Thomas Schreiber

               This module could do with some serious
               reimplementation. Should anyone have the engergy to do
               so, I recommend that in pretty-printing mode, the block
               format is converted to annotations so that e.g., an
               Emacs interface can insert linebreaks and indentation
               where appropriate. *)


(* Annotations
   -----------
   are sent out by the pretty printer to efficiently communicate with
   a user-interface such as the generic Emacs interface for theorem
   provers developed by Goguen, Kleymann, Sequeira and others.
   See the LFCS Technical Report ECS-LFCS-97-368 for details.

   At the user level, 

     Configure AnnotateOn;

   tells the PrettyPrinter to output annotations. After

     Configure AnnotateOff;

   annotations are no longer printed. This is the default.

 *)

(* We use the qwertz toolbox' Pretty module to format the output. The  *)
(* algorithm is based on Paulson, ML for the Working Programmer,       *)
(* section 8.9. Notice that if linelength=0, this effectively turns    *)
(* pretty printing off                                                 *)

(* Instead of sending everything to the outstream, we send it to a     *)
(* pretty-print stream.                                                *)

functor FunPretty (structure Term : TERM
		   structure Context : CONTEXT
		   structure LegoFormat : LEGOFORMAT
		   sharing 
		   	   type Term.cnstr
			      = Context.cnstr
			      = LegoFormat.cnstr
		   and 
		   	   type Term.binding
			      = Context.binding
			      = LegoFormat.binding
		   and 
		   	   type Term.visSort
			      = LegoFormat.visSort
		   ) 
(* *** *
structure Pretty 
 * *** *)
	: PRETTY 
 =
struct

	type cnstr = Term.cnstr
	type binding = Term.binding
	type visSort = Term.visSort

	type context = Context.context
	
  local
(* other code moved from here to LegoFormat; so reimport it here *)
      open LegoFormat 
  in

(* ***************** needed in Umachine.sml ****************** *)

    val prnt = prnso o format
    val legoprint = prnso o postlf o format (* legoformat *)
    val print_expand = AvoidPrettyPrinting (prnso o format_expand)
    val prnt_red = prnso o format_red

(* ***************** ********************** ****************** *)

(*  val indent = indent *) 
(*  val input_line = Format.input_line *) 

    val print_words = prnso o postlf o block0 o format_words

    val isPrettyPrinting = isPrettyPrinting
    val SetLineWidth = SetLineWidth

    fun SetPrettyPrinting isActive =
      (LegoFormat.SetPrettyPrinting isActive;
       print_words ["Pretty","printing","is","now",
		    if isActive then "enabled" else "disabled"])


(* ************** already defined in printing.sml ********************* *
    val message = prnso o postlf o string
    fun loudmessage str = let
			     val lstr = if hasAnnotations () 
			      	      	   then "\254"^str^"\255" 
				    	else str
			  in
			     message lstr
			  end
 * ************** already defined in printing.sml ********************* *)

(* ************** needed thereafter ********************* *)

    val prnt_vt = prnso o format_vt 
    val prnt_vt_expand = AvoidPrettyPrinting (prnso o format_vt_expand)
    fun os_prnt_exp os  = AvoidPrettyPrinting ((print os) o format_tuples)
    fun os_prnt_red os  = AvoidPrettyPrinting ((print os) o format_red)

(* *** printers testing isInteractive(): formatting defined in {lego}format.sml *** *)
    fun prnt_goals gs = List.app prnso (format_goals gs)

    fun prnt_defn id v t = List.app prnso (format_defn id v t)
(*    if interactive() 
	then (prnso (block (2, [string "defn", break 2] @
			    (format_words [id,"="]) @
			    [break 1, legoformat v]));
	      prnso (block (2, (break 6) ::
			    (format_words [id,":"]) @
			    [break 1, legoformat t])))
      else prnso (block (8, (format_words ["defn ",id,"=","...",":"]) @
			 [break 1,legoformat t]))
*)			     
    fun prnt_decl v id = prnso o (format_decl v id)
    fun print_cannot_assume id = prnso o postlf o (format_cannot_assume id)
    fun print_value id = prnso o postlf o (format_value id)
    fun print_type id = prnso o postlf o (format_type id)
    fun print_refine g = prnso o (format_refine g)

    fun print_qrepl v lhs rhs =
      (prnso (block (2, [string "Qrepl", break 2, legoformat v]));
       prnso (block (2, [format lhs, break 1, string "=>",
			 break 1, legoformat rhs])))

    fun print_bind f = prnso o (format_bind f)

(* ********** moved from Namespace ********* *
 * printing: needed by toplevel.sml
 * refactored 2011     lego.grm.sml 
 * ******** *) 

   fun prt_context_ elideFlg = Context.do_cxt (print_bind elideFlg) 

   fun prt_context_dpth_ elideFlg n = Context.do_cxt_dpth (print_bind elideFlg) n 

   fun prt_context_nam_ elideFlg nam = Context.do_cxt_nam nam (print_bind elideFlg) 

   fun prt_context_ref_ elideFlg br = Context.do_cxt_ref br (print_bind elideFlg) 

(* ******** *) 

   val prt_context = prt_context_ ElideDfns

   val prt_context_dpth = prt_context_dpth_ ElideDfns

   val prt_context_nam = prt_context_nam_ ElideDfns 

   val prt_context_ref = prt_context_ref_ ElideDfns 

   val prt_decls = prt_context_ OmitDfns

   val prt_decls_dpth = prt_context_dpth_ OmitDfns

   val prt_decls_nam = prt_context_nam_ OmitDfns 

   val prt_marks = prt_context_ Marks

(* *** end: moved from Namespace *** *)

  end
end;

(*
structure Pretty = FunPretty (structure LegoFormat = LegoFormat);
 *)
(* open Pretty; *)

