(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* modified 

   09 nov 2009 printing lifted from utils.sml to here 

*)

(* 
Pretty printing.  From Paulson, ML for the Working Programmer.
Page 312.  A few things have been changed, to adjust them to my taste:

    1) The type T is now called "block"
    2) The Format module is now a structure, instead of functor, to make it 
easy to pretty print with blocks composed out of types from different structures.
    3) The print procedure no longer prints a newline after pretty printing
the block.   This allows blocks to be pretty printed "in line".

author: Tom Gordon <thomas.gordon@gmd.de>

CHANGES
-------

28 Jun 1996 replacement for BASE's input_line

28 Dec 1995 supporting multiple print commands in one line 

20 Dec 1995 Extended the datatype block with linebreaks

30 Nov 1994 Thomas Schreiber <lego@dcs.ed.ac.uk>
            The variable active dictates whether pretty printing is desired

*)

structure Format : FORMAT =
    struct
	datatype block = 
	    Linebreak
	  | String of string
	  | Block of block list * int * int 	(* indentation, length *)
	  | Annotate of int list      		(* path for PBP *)
	  | Break of int;			(* length *)


	val indent     = ref 4  (* spaces *)
	val linelength = ref 78
	val active     = ref true
	val space      = ref (!linelength)

(* Add the lengths of the expressions until the next Break; if no
Break then include "after", to account for text following this block.
*)
	fun breakdist (Linebreak :: bs,after)     = 0 
	  | breakdist (String s :: bs, after)     = 
	         size s + breakdist (bs, after)
	  | breakdist (Block(_,_,len)::bs, after) = 
	            len + breakdist(bs, after)
	  | breakdist (Annotate _ :: bs, after)   = 
	    	          breakdist (bs,after)
	  | breakdist (Break _ :: bs, after)      = 0
	  | breakdist ([], after)                 = after;

	fun length  Linebreak       = 0
	  | length (String s)       = size s
	  | length (Block(_,_,len)) = len
	  | length (Annotate _)     = 0
	  | length (Break len)      = len; 

	val linebreak = Linebreak
	and string = String  
	and annotate = Annotate    
	and break = Break 

	fun block (indent,bs) =
	    let fun sum( []  , k) = k
		  | sum(b::bs, k) = sum(bs, length b + k)
	    in  Block(bs,indent, sum(bs,0))  end; 

	fun block0 bs = block (0, bs)

	fun postlf bl = block0 [bl,linebreak]
    
	fun SetLineLength ll = (space := !space + ll - !linelength;
				linelength := ll)

(* *** is this a problem??? *** *

	fun inputLine is = 
		(* TextIO has changed the type of inputLine *)
	    let fun inputLine_  (SOME s) = s
                  | inputLine_    NONE   = ""
            in  
		inputLine_  (TextIO.inputLine is)
	    end

	fun input_line is = let
			       val result = inputLine is
			    in
			       space := (!linelength);
			       result
			    end

 * *** ********************* *** *)

       	local 

	   fun processLine (SOME s) = s
	     | processLine   NONE   = ""

	in 

	   fun inputLine is = let 
	       		      	 val txtopt = TextIO.inputLine is
	       		      	 val result = processLine txtopt
			      in 
			       	 space := (!linelength);
			       	 result
			      end 
			

	end

(* ****************** pushed into annotation.sml: annotation tags ********************* *

   val BEGININPUTLINE = " AAA   "(*"\249"*)
   val BEGINPBP       = " PPP   "(*"\250"*)
   val ENDPBP 	      = "   QQQ "(*"\251"*)
   val ENDPATH 	      = " III   "(*"\252"*)
   val BEGINBIND      = " ZZZ   "(*"\253"*)
   val BEGINLOUD      = " MMM   "(*"\254"*)
   val ENDLOUD 	      = "   NNN "(*"\255"*)

   val PATHMARKER=252
   
      fun promptAnnotating s = (if isAnnotating() then (s^BEGININPUTLINE) else s)
  
      fun pbpAnnotate s = BEGINPBP^s^ENDPBP
  
      val annotate_path_end = ENDPATH

      fun formatAnnotating bl = (if isAnnotating() then string BEGINBIND else bl)
  
      fun stringAnnotating s = (if hasAnnotations() then (BEGINLOUD^s^ENDLOUD) else s)
  
      fun path_wrap l bls = 
	  if isAnnotating () then 
	      (annotate (rev l))::(bls@[annotate [PATHMARKER]]) (* *** below: str252 *** *)
	  else bls 
      (* This is a hack from legoformat.sml: pbpAnnotate adds the 250 and 251 codes. *)


	local (* all of these can be lifted out now *)
		
	    val last_path = ref ([]: int list)

	    fun init_path () = (last_path:=[])
	
	(* *** a path is a Proof-by-pointing structure for indexing extents ***** *)
	    fun compress_path t =

	    	let fun slice i old [] = [i]
		      | slice i [] new = i::new
		      | slice i (p::old) (n::new) = 
		      	if p = n then slice (i+1) old new else i::n::new
	    	in 

	(* ***** fn x => chr (x+128) is for Proof-by-pointing under PG/PBP ***** *)
		    let val path' = slice 0 (!last_path) t
		    in (last_path := t; 
		        String.implode (List.map (fn x => chr (x+128)) path'))
		    end
	    	end
	    
	    fun annotate_path t = pbpAnnotate (compress_path t)

	(* **** str252 is for path_wrap triggering PBP markup: \250 and \251 **** *)
	    fun str252   []   = false
    	      | str252 (h::t) = h = PATHMARKER;
	(* **** str252 s = s <> [] andalso (hd s) = 252 *** *)

	in

	    fun markup_path s = if (str252 s) 
				    then annotate_path_end 
			          else 
				    annotate_path s

	    fun init_path () = (last_path:=[])
	
	end; 

 * ********************** pushed into annotation.sml: annotation tags ******************* *)

	fun print os b  =
	    (let 
	    (* ******************************************** *
		fun blanks 0 = () (* TextIO.flushOut os *)
		  | blanks n = (TextIO.output(os," "); 
		    	       	space := !space - 1; 
				blanks(n-1))
	     * ******************************************** *)
	        fun blanks n = if n <= 0 then () 
				else (TextIO.output(os, Utils.StringUtil.spaces n);
				      space := !space - n)

		fun newline () = (TextIO.output(os,"\n"); (* or another mark? *)
		    	       	  space := (!linelength);
				  TextIO.flushOut os) (* always flush after a newline *)

		fun printing ([], _, _) = TextIO.flushOut os (* always flush when done *)

		  | printing (b::bs, blockspace, after) =
		    (case b of
			 Linebreak => newline()

		       | String s => (TextIO.output(os,s); space := !space - size s)

		       | Block(bbs,indent,len) =>
			     printing(bbs, !space-indent, 
				      breakdist(bs,after))

		       | Annotate s => TextIO.output(os, Annotate.markup_path s) (* *** *)

		       | Break len => 
			     if ((len + breakdist(bs,after) <= !space) orelse
				 (not (!active)))
				 then blanks len
			     else (newline(); 
				   blanks((!linelength)-blockspace));
				 printing (bs, blockspace, after)
			)

	    in  

               (Annotate.init_path(); (* *** annotate.sml *** *)
		printing([b], (!linelength), 0))

	    end);

(* old:	fun prtmsg out s  = print out (block0 [string s,linebreak]) *)

	fun prtmsg out s  = print out (postlf (string s))


(* **** this is redundantly duplicated as message in pretty.sml *** *)

(* ********* pulled from LegoFormat: interactive flag check ************** *)

    fun formatAnnotating bl = (if Annotate.isAnnotating() 
    			      	  then string Annotations.BEGINBIND 
				else bl)
  
    fun formatInteractive bls bls' = (if Annotate.interactive() then bls else bls')

(* ********* pulled from Pbp: documentation of path annotations ********** * 
    Documentation:

    The modules Format,LegoFormat,Pretty are responsible for the following annotations:

      o Application f a1 ... an
          Internal Represenation: PrApp (PrRef "f", [("a1",_), ..., ("an",_)])
          Annotations: 1   |-> f
                       2   |-> a1 ... an
                       2 i |-> ai
		       
      o Pi Abstraction {x1,...xn:A}B
	  Internal Represenation: PrBind ([x1,...,xn], (Pi,Vis), A, B) 
	  Annotations: 1   |-> x1,...,xn                
	               1 i |-> xi        if n>1                         
                       2   |-> A                               
                       3   |-> B 

      o Implication A->B
          Internal Represenation: PrBind ([], (Pi,Vis), A, B) 
          Annotations: just like application with (op->) A B i.e.,
                       1   |-> ->
                       2   |-> A B
		       2 1 |-> A
		       2 2 |->   B
 * ************************************************************************ *)

    fun path_wrap l bls = 
	  if Annotate.isAnnotating () then 
	      (annotate (List.rev l))::(bls@[annotate [Annotations.PATHENDMARKER]]) (* *** str252 *** *)
	  else bls 
   (* This is a hack from legoformat.sml: pbpAnnotate adds the 250 and 251 codes. *)

(* ************************************************************************ *)
    end; (* struct *) 

