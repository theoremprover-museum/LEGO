(* $Id: interface.sml,v 1.9 1998/09/16 14:32:58 tms Exp $ *)

functor FunInterface 
        (structure Error:ERROR
   	 structure Modules:MODULES 
   	 structure PromptKnots:CONORKNOTS 
	 structure Pos:POS
	 structure LegoParser:PARSER
	 structure LegoTokens:Lego_TOKENS
	 sharing 
	 	 type LegoParser.arg = Modules.stamp
	 and	  
	 	 type LegoParser.pos = Pos.pos
	 and	 
	 	 type LegoTokens.token = LegoParser.Token.token  
	 and	 
	 	 type LegoTokens.svalue = LegoParser.svalue  
	)

   :     sig

(* ********* parsers cached in registers, to avoid recursive modules! ******* *
   	     type stamp 		
             val legof : stamp -> (unit -> unit) -> unit
             val legos : string -> unit
 * ******************* * **************************************************** *)

             val lego_parser : (unit -> unit) -> (int -> string) -> unit

(* ********* moved to main.sml ********** *
             val lego   : unit -> unit

             val legoML : unit -> unit
 * ********* ***************** ********** *)
         end
(* *** * 
structure LegoInterface
 * *** *)
   =

struct

       type stamp = Modules.stamp 

 local

	(* show non-interactive *)
 	val pre_opening = (Annotate.interactive_push o Annotate.SuspendAnnotations) 

	val pre_closing = (Annotate.ResumeAnnotations o Annotate.interactive_pop)

       val prnl	       = Printing.prnl
       val message     = Printing.message
       val loudmessage = Printing.loudmessage

       val legocomment = Utils.StringUtil.legocomment
       val dquote = Utils.StringUtil.dquote

       open Utils.Except
	
   fun parse exiting (lookahead, reader:int->string, filenamestamp) =
     let
        val error = Pos.errmsg "Lego parser"
	val     _ = Pos.init_lno()
        val dummyEOF = let val zzz = !Pos.lno
		       in  LegoTokens.EOF(zzz,zzz)
		       end

	fun reachEOF tok = LegoParser.sameToken(tok,dummyEOF)

	fun invoke lexer = 
	   LegoParser.parse(lookahead,lexer,error,filenamestamp)

        fun loop lexer =
	  let val (result,lexer) = invoke lexer
	      val (nextToken,lexer) = LegoParser.Stream.get lexer
	      val _ = PromptKnots.do_all_knots (fn _ => true) 
	  in if reachEOF(nextToken)
	     	then exiting()
	     else loop lexer
	  end
     in loop (LegoParser.makeLexer reader)
     end

  in

(* file parser: try to get the control flow correct!!! *)

    local 

     fun unexpected msg s = (failwith("Unexpected error "^msg^":\n"^s))

     fun unwind () = (failwith"Unwinding to top-level")


     (* file reader *)       (*        **** ****************  ***** *)
     fun file_reader in_str = fn _ =>  case (TextIO.inputLine in_str) of
				      	    SOME s => s
			      		  | NONE   => raise Option 
			     (*        **** ****************  ***** *)
                    			


    in 

    fun legof filnamstmp clos = 
      let

        val filnam = Modules.getFileName filnamstmp

        val DepChecking = Modules.isDepChecking filnamstmp

	fun exiting () = (prnl(); message("Done reading file "^filnam^"..."); prnl())

        fun readIt in_str = (parse (fn()=>()) (15, file_reader in_str, filnamstmp))

        fun opening msg filenam = 
			     let 
	    	   	     	 val in_str = TextIO.openIn filenam
			     in 
			        (loudmessage(legocomment(msg)); 
				 pre_opening(); 
				 in_str)
			     end handle IO.Io s 
			     	 => unexpected msg (#name s);

        fun openIt filenam = let 
	    	   	     	 val msg = if DepChecking 
				     	   then "checking "^filenam
				 	   else "opening file "^filenam
			     in 
				 opening msg filenam
			     end 

	val t = Utils.Timing.start_timer()
	fun print_timer() = Utils.Timing.makestring_timer t

	fun closing msg in_str = 
			     let 
	    	   	     	 fun act () = if DepChecking 
				     	      then ()
				 	      else loudmessage(legocomment(msg));
			     in 
			        (pre_closing(); 
				 TextIO.closeIn in_str; 
				 act())
			     end handle IO.Io s 
			     	 => unexpected msg (#name s);

	fun closIt in_str = let 
	    	   	     	 val msg = "closing file "^filnam^"; "^(print_timer())
			     in
				 closing msg in_str
			     end
				 
	fun err_closing s = (message("Error processing file "^filnam^": "^s);
			     unwind())

	fun success () = () (* exiting () *)
	(* loudmessage("End of file found") anything needed? *)

      in

	(
	 (try_raise_finally openIt readIt closIt filnam) 

	  handle  exn as Modules.DepCheckDone(d) 
	 (* no need to handle this: except for self-documentation and catch-all clause below *)
				=> raise exn (* Modules.DepCheckDone(d) *)

		| Option        => success() (* this is where the file ends! *)
		(* *** exn Option arises from valOf wrapping inputLine above *** *)

		| Error.error s => Error.ErrorHandler s (* file already closed ?*)

		| Failure s 	=> err_closing s
		| IO.Io s 	=> err_closing (#name s)
		| Bug s 	=> err_closing s
                | exn 		=> err_closing (* what else could it be now? *)
                  ("\nLEGO detects unexpected exception named "^dquote(General.exnName exn))
	)

        before (clos())

      end

    val _ = Modules.legoFileParser := legof;   (* Used to implement Make etc. *)

    end (* file parser *)


(* parser, for strings and interactive top-level *)
 
    fun lego_parser exiting reader = 
    	parse exiting (0,reader,Modules.initStampString())


(* string parser *)
(* NOTE: exceptions from string parser are      *
 * thrown to next outer file parser or toplevel *)

    local

    	fun exiting () = () (*(prnl(); message"Done reading string..."; prnl())*)

    	(* string reader *)
    	fun string_reader str = let val next = ref str
			      	in  fn _ => !next before next := ""
			    	end

    in 	
    	fun legos str = lego_parser exiting (string_reader str)

	val _ = Modules.legoStringParser := legos; (* Used to implement Logic *) 
    end
    

  end;
end;

(* now build it *)

structure Interface = 
	  FunInterface (structure Error=Error
	  		structure Modules=Modules
	  		structure PromptKnots=PromptKnots
	  		structure Pos=Pos
	  		structure LegoTokens=LegoLrVals.Tokens
	  		structure LegoParser=LegoParser
	  ); 
