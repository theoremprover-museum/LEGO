(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* error.sml    Error handling for LEGO
   Author: Thomas Schreiber <tms@dcs.ed.ac.uk>
   $Log: error.sml,v $
   Revision 1.7  1997/11/24 11:00:57  tms
   merged immed-may-fail with main branch


   Revision 1.6  1997/08/25 10:59:15  tms
   Immed fails if no progress has been achieved

   Revision 1.5  1997/07/11 13:27:06  tms
   Qrepl will fail if the LHS does not occur in the goal

   Revision 1.4  1997/05/08 13:46:36  tms
   Extended expansion mechanism relative to a path

   Revision 1.3  1997/02/17 17:39:10  tms
   added support for failed Assumption command

*)

functor FunError(
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
structure Error
 * *** *)
	: ERROR
 = 

struct

		type cnstr = Term.cnstr

	    datatype ErrorClass
		= ASSUMPTION | TYPEAPPLN | APPLNTYPE | APPLNNFUN |
		PATH | REPLLHS | IMMED

	    datatype ErrorSignal = Error of ErrorClass*(int option)*(cnstr list)

	    exception error of ErrorSignal

	    fun mkTYPEAPPLN  c = Error(PATH, NONE, [c])
	    fun mkPATH       c = Error(PATH, NONE, [c])
	    fun mkAPPLNTYPE cs = Error(APPLNTYPE, NONE, cs)
	    fun mkAPPLNNFUN cs = Error(APPLNNFUN, NONE, cs)
	    val mkIMMED        = Error(IMMED, NONE, [])
	    fun mkASSUMPTION n = Error(ASSUMPTION, SOME n, [])
	    fun mkREPLLHS  n c = Error(REPLLHS, SOME n, [c])

	local

		val succ = Utils.Counting.succ 
		val spaces = Utils.StringUtil.spaces

	(* 2011: sharing constraint violated??? yes, see above!!! *)
	    structure ErrorFormat = FunErrorFormat(
	    	      		    structure Term = Term
	    	      		    structure LegoFormat = LegoFormat
	    	      		    ) 
        
	    open ErrorFormat 

	in
	    fun append a b = a @ b

	    fun prefix s
		= print o (block 2)
		      o append [formatString "Error"]
		      o append (formatInteractive [] [formatWord" in file"])
		      o append [formatString(": "^s) ,newline]


	    fun leftmargin n bl
		= let
(*
                      fun space_n i cs = if i < 0 then cs else space_n (i-1) (#" "::cs)
		      val s = implode (space_n n []) (* *** adds (n+1) blanks!!! *** *)
 *)
		      val s = spaces (succ n) (* *** adds (n+1) blanks!!! *** *)
		  in
		      block n ((formatWord s)::bl::[newline])
		  end

	    fun ErrorHandler_ (ASSUMPTION,(SOME g):int option,[])
		= prefix ("Goal "^(Int.toString g)^
		" cannot be closed by an instance of any assumption") []

              | ErrorHandler_ (IMMED,_,[])
		= prefix ("No goal can be closed by an instance of \
			  \any assumption") []

	      | ErrorHandler_ (TYPEAPPLN,g,[c]) (* c should be Concrete, not Abstract? *)
		= prefix " 'Type' must be either ambiguous or relative \
			    \to a universe i.e., a natural number or an \
			  \identifier, \
			    \but cannot refer to the term"
		[leftmargin 2 (cnstr_format false c), (* #1 (fEval c) *)
		 formatString "Enclose 'Type' in parenthesis to achieve \
		     \full typical ambiguity."]
	      | ErrorHandler_ (APPLNTYPE,g,[v,t,v',t'])
		     = prefix "Type mismatch in attempting to apply"
		     [leftmargin 3 (cnstr_format true v),
		      formatString "with domain type", newline,
		      leftmargin 3 (cnstr_format true t),
		      block 3 [formatWord "to ",cnstr_format true v'], newline,
		      block 3 [formatWord " : ", cnstr_format true t']]

	      | ErrorHandler_ (APPLNNFUN, g, [c,T])
		= prefix "Application of a non-function"
		[leftmargin 3 (cnstr_format true c), 
		 block 3 [formatWord " : ", cnstr_format true T]]

	      | ErrorHandler_ (PATH, g, [c])
		= prefix "Illegal path specified"
		[formatString "The term", newline,
		 leftmargin 3 (cnstr_format false  c),
		 formatString "has been addressed with an illegal path"]

              | ErrorHandler_ (REPLLHS, (SOME g), [c])
		 = prefix "Qrepl Tactic"
		 [formatString "LHS", newline,
		  leftmargin 3 (cnstr_format false c),
		  formatString ("doesn't occur in goal "^(Int.toString g))]

              | ErrorHandler_ (IMMED, _, _)
		 = prefix "Immed Tactic failed" []

	      | ErrorHandler_ _ = print (formatString "Unexpected error!")
	end

	fun ErrorHandler (Error errdata) = ErrorHandler_ errdata
end




