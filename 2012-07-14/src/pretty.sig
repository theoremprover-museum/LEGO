(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* *********************************************************************** *
   refactoring shar_pretty.sml:signatures 
 * *********************************************************************** *)

signature PRETTY =
  sig

	type cnstr 
	type binding 
	type visSort 

	type context 

    val legoprint : cnstr -> unit

    val print_words  : string list -> unit
    val print_expand : cnstr -> unit

    val print_cannot_assume : string -> (cnstr*cnstr) -> unit
    val print_value  : string -> cnstr -> unit
    val print_type   : string -> cnstr -> unit
    val print_qrepl  : cnstr -> cnstr -> cnstr -> unit (* only in tactics! *)
    val print_refine : int -> cnstr -> unit (* only in synt! *)

(* *** moved from Namespace; needed by lego.grm, toplevel.sml *** *)

    val prt_marks   : context -> unit

    val prt_context : context -> unit
    val prt_context_dpth : int -> context -> unit
    val prt_context_nam : string -> context -> unit

    val prt_decls : context -> unit
    val prt_decls_dpth : int -> context -> unit
    val prt_decls_nam : string -> context -> unit

(* *** needed by toplevel.sml *** *) 

    val prt_context_ref : binding -> context -> unit

(* *** ********************** *** *)

    val prnt : cnstr -> unit (* only in Umachine! *)

    val prnt_vt : (cnstr*cnstr) -> unit
    val prnt_vt_expand : (cnstr*cnstr) -> unit

    val prnt_red : cnstr -> unit
    val prnt_defn : string -> cnstr -> cnstr -> unit
    val prnt_decl : visSort -> string -> cnstr -> unit

    val prnt_goals : (int * cnstr) list -> unit (* tests isInteractive() *)

    val os_prnt_exp : TextIO.outstream -> cnstr -> unit (* for Modules *)
    val os_prnt_red : TextIO.outstream -> cnstr -> unit (* for Modules *)

(* **************** already defined in printing.sml ***************** *
    val message : string -> unit
    val loudmessage: string -> unit
 * ***************** ***************************** ****************** *)

    val SetPrettyPrinting : bool -> unit
    val isPrettyPrinting  : unit -> bool
    val SetLineWidth 	  : int -> unit

  end  

(* The choice of names are mainly for historic reasons and should be   *)
(* adapted one day.

   _exp means that terms will be printed in extended form *)

(* The expanded version is aimed towards the creation of object  *)
(* files. As Tim Heap has pointed out to me, these should not be *)
(* pretty-printed                                                *)

