(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

functor FunErrorFormat (
	structure Term:TERM
	structure LegoFormat:LEGOFORMAT
	sharing 
		type Term.cnstr 
		   = LegoFormat.cnstr 
	and 
		type Term.binding
		   = LegoFormat.binding
	and 
		type Term.visSort
		   = LegoFormat.visSort
	) 
(* *** * 
structure ErrorFormat
 * *** *) 
	: ERRORFORMAT
 =
struct

	type cnstr = LegoFormat.cnstr
	type format = LegoFormat.block
	val std_err = TextIO.stdOut (* stdErr? *)
		
	fun print   bl = LegoFormat.print std_err (LegoFormat.postlf bl)
	fun block n bl = LegoFormat.block (n,bl)
	val newline    = LegoFormat.newline

	val cnstr_format = LegoFormat.format_cnstr (* !!! *)

	val formatWord = LegoFormat.string

	fun formatString s
	    = LegoFormat.block0 (LegoFormat.format_words
			            (String.tokens Char.isSpace s))
	val formatInteractive = LegoFormat.formatInteractive
end

