(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* format.sig *)

signature FORMAT = 
    sig
	type block

	val string        : string -> block
	val linebreak     : block
	val break         : int -> block
	val annotate      : int list -> block

	val block         : int * block list -> block
	val block0        :       block list -> block
	(*  block0 bs = block (0,bs) *)
	val postlf	  : block -> block
	(*  postlf b = block0 [b, linebreak] *)

(* ****************** pulled from LegoFormat/Pbp ******************* *)

	val formatInteractive : block list -> block list -> block list
	val formatAnnotating  : block -> block
	val path_wrap         : int list -> block list -> block list

	val active        : bool ref (* do we want pretty printing? *)
        val indent        : int ref
        val SetLineLength : int -> unit

	val inputLine    : TextIO.instream -> string

	val print         : TextIO.outstream -> block -> unit

	val prtmsg        : TextIO.outstream -> string -> unit
    end;

(* ******************** pushed into annotate.sml ******************* *

	val stringAnnotating  : string -> string
	val promptAnnotating  : string -> string
	val pbpAnnotate   : string -> string

 * ******************** ********************** ********************* *)

