(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* now begin in earnest *)

signature LEGOFORMAT = 
    sig

	type cnstr (* = Term.cnstr *)
	type binding (* = Term.binding *)

	type visSort (* = Term. visSort *)

	type block (* = Format.block *)

	val prompt : TextIO.outstream -> unit (* output *** "Lego> " itself *** *)

	datatype dfnsPrnt = OmitDfns | ElideDfns | ShowDfns | Marks 

	eqtype prCnstr 

(* 
  datatype prCnstr = PrBot
    | PrProp
    | PrType  of Universes.node
    | PrRef   of string
    | PrRel   of int
    | PrApp   of prCnstr * ((prCnstr * prntVisSort) list)
    | PrBind  of string list * bindVisSort * prCnstr * prCnstr
    | PrVar   of int * prCnstr
    | PrTuple of prCnstr * (prCnstr list)
    | PrProj  of projSort * prCnstr
    | PrRedTyp of instrs * prCnstr
    | PrThry
    | Pr_theory of (string * prCnstr * prCnstr) list
    | PrCast of (string list * bindVisSort * prCnstr) list * prCnstr * prCnstr
          (* rewrite  reductions  *)
    | PrRedBod of (prCnstr * prCnstr) list  (* rewriting reductions *)

 *)

  exception getPrCnstr

  val getPrArr : prCnstr -> prCnstr * prCnstr

  val mkPrArr  : prCnstr * prCnstr -> prCnstr 

  val getPrPi  : prCnstr -> string list * prCnstr * prCnstr

  val mkPrPi   : string list * prCnstr * prCnstr -> prCnstr 

  val getPrLet : prCnstr -> string list * prCnstr * prCnstr

  val mkPrLet  : string list * prCnstr * prCnstr -> prCnstr 

(*
  datatype granularity = explicit | implicit 
	   	       | tuples	(* explicit, but non-dependent tuples * 
		       	 	 *  will have no typing information   *) 
 *)

	val whnfr : (cnstr -> cnstr) ref
	val SetPrettyPrinting: bool -> unit
	val isPrettyPrinting : unit -> bool
	val SetLineWidth     : int -> unit

	val AvoidPrettyPrinting : ('a -> unit) -> 'a -> unit  

	val newline       : block
	val postlf        : block -> block
	val block         : (int*block list) -> block
	val break         : int -> block
	val string        : string -> block
	val block0        : block list -> block

	val format_words     : string list -> block list

	val format_cnstr : bool -> cnstr -> block 
	(*  format_cnstr true  yields an extended form
	    format_cnstr false yields the standard form *)

(* 
	val format_           : granularity -> bool -> cnstr -> block
 *)
	val format           : cnstr -> block (* default: format implicit *) 
	val format_tuples    : cnstr -> block

	val legoformat       : cnstr -> block (* postlf o format *)
	val format_expand    : cnstr -> block
	val format_goal      : (int*cnstr) -> block
	val format_vt        : (cnstr*cnstr) -> block
	val format_vt_expand : (cnstr*cnstr) -> block
	val format_red       : cnstr -> block
	val format_decl      : visSort -> string -> cnstr -> block
	val format_cannot_assume : string -> (cnstr*cnstr) -> block
        val format_value     : string -> cnstr -> block
	val format_type      : string -> cnstr -> block
	val format_refine    : int -> cnstr -> block

	val format_bind      : dfnsPrnt -> binding -> block

	val formatInteractive : block list -> block list -> block list
	val format_defn      : string -> cnstr -> cnstr -> block list (* interactive *)
	val format_goals     : (int*cnstr) list -> block list (* interactive *)

	val print            : TextIO.outstream -> block -> unit 
	val prnso            : block -> unit 

(*	val ffp         : granularity ->  bool -> cnstr -> prCnstr *)
	val ffp_pbp         : cnstr -> prCnstr
    end;

