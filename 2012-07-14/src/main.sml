(* ************************************************************* *
   porting to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

 * ************************************************************* *)

(* This structure localises all the SML-NJ specials, except UNSAFEeq in Utils *)

(* needs
	SMLofNJ structure for lego's top-level loop and exportML/exportFn
	SMLofNJ library Compiler structure for val "banner"
        Unix structure: execute and streamsOf for fun "date"
*)

(** generate core standalone Unix process, and export toplevel loop  **)
(*

	needs a complete sorting out, vis-a-vis the new semantics for exports

	  val LEGO : (string * string list) -> unit
 	  val main : (string * string list) -> OS.Process.status

	main just wraps LEGO as a Unix process
	LEGO expects argv to be filenames, and runs "Make" on them

	some better command line processing would be nice!
*)

(* *** * 
functor FunMain 
        (structure Error:ERROR 
   	 structure Init:INIT
   	 structure Modules:MODULES 
   	 structure Pbp:PBP
	 structure Interface:
	 	   sig 
	 	       val lego_parser : (unit -> unit) -> (int -> string) -> unit 
		   end
	)

   :     sig

             val lego   : unit -> unit

             val legoML : unit -> unit 

	     val make_lego : bool -> string -> unit

         end
 * *** *)

structure Main

   =

struct

  local

       val prnl	       = Printing.prnl
       val print       = Printing.prs
       val message     = Printing.message
       val loudmessage = Printing.loudmessage

       val legocomment = Utils.StringUtil.legocomment
       val squote      = Utils.StringUtil.squote
       val dquote      = Utils.StringUtil.dquote

       open Utils.Except 

       fun init() = (Init.InitXCC() ; Pbp.InitPBP())

       val make = List.app (Modules.Make)

  in 

(* interactive top-level parser *)

    local

	(* no longer in SML'97; is it still needed? Yes? *)

     	exception Interrupt = SML90.Interrupt

        fun catchTopCont() =
	(Unsafe.topLevelCont :=
	 SMLofNJ.Cont.callcc
      		 (fn k => (SMLofNJ.Cont.callcc (fn k' => (SMLofNJ.Cont.throw k k'));
			  	raise Interrupt)))

     	val std_out = TextIO.stdOut
     	val std_in  = TextIO.stdIn

   	fun exiting () = (prnl(); message"Dropping out of LEGO..."; prnl())

        fun backtoOS () = (message"... back to invoking process"; prnl());

        fun backtoML () = (message"... back to ML"; prnl());

     	(* interactive line reader *) 
     	fun line_reader in_str = fn _ => (LegoFormat.prompt std_out;
			      	       	  TextIO.flushOut std_out;
					  Format.inputLine in_str
					  )

   	fun lego_input () = Interface.lego_parser exiting (line_reader std_in)

    in  

        fun lego() =
	(catchTopCont();
	 Annotate.Interactive();
	 lego_input()
(* what could go wrong? *)
	 handle Error.error s 	=> (Error.ErrorHandler s; lego())
	      | Failure s   	=> (message("Lego Error: "^s); lego())
	      | Bug s 		=> (message s; lego())	       (* *** fatal? drop to ML *** *)
	      | IO.Io s 	=> (message (#name s); lego()) (* *** fatal? drop to OS *** *)
	      | LegoParser.ParseError 
				=> (lego())

(* ********** a class of errors which cannot occur??? **** *
	      | LegoLex.LexError 
	      			=> (lego())
	      | Empty s 	=> (message("(* Empty "^s^" raised during interactive *)")
			           	; lego())
	      | List.Empty  	=> (message("(* List.Empty raised during interactive *)")
			           	; lego())
 * ******************************************************* *)

	      | exn 		=> (message("\nLEGO detects unexpected exception named "
				   	    ^dquote(General.exnName exn)); 
			  	    lego()) (* *** fatal? do not restart? *** *)
	 )
	  handle Interrupt => (message"\nInterrupt... "; lego()); (* OK, resume *)

        fun legoOS () = (lego(); backtoOS()) 

        fun legoML () = (lego(); backtoML()) 

    end; 

    local 

       	  val lego_argc = legocomment"*** lego ***"
       	  val legoML_argc = legocomment"*** legoML ***"

       	  fun arch () = (* get current destination for binaries *)
	      case (OS.Process.getEnv "LEGOARCH")
       		of (SOME s) => s 
        	 |  NONE    => (message"No entry `LEGOARCH' in environment;\
                                \ core images placed in subdirectory `bin'.";
			        "../bin")

       	  fun date () = (* get current date *)
      	      let 
        	  val unix_date = "/bin/date"
		  val proc_id   = Unix.execute (unix_date,[])
		  val (is,os)   = Unix.streamsOf proc_id
		  val date      = TextIO.inputLine is
		  val         _ = (TextIO.closeIn is; TextIO.closeOut os)
		  val         _ = Unix.reap proc_id
      	      in 
        	  (case date of (SOME d) => d (* *** curse of inputLine !!! *** *)
                     	     |   NONE   => "")
      	      end

       	  fun head msg = (* make header banner *)
      	      let 
         	  val version = Compiler.version
         	  val system = #system version
         	  val [maj,min] = List.map Int.toString (#version_id version)
         	  val banner = system^", Version "^maj^"."^min
      	      in  
		  (prnl();
       		   (*print "Standard ML with LEGO\n";*)
       		   print ("Generated  "^date());
       		   print ("using "^banner^"\n");
       		   if msg <> "" then print (msg^"\n") else ();
       		   print "use command 'Help' for info on new commands. "; 
		   prnl())
      	      end

       	  fun LEGO (argc,argv) msg lego = (message argc; head msg;
    	     		       	       	   init();
			       	       	   make argv; (* load the files *)
			       	       	   lego() handle IO.Io s => ())
      in  
      	  
	  fun make_lego b msg = 
	      let 
	      	  val bin = arch()
	      	  val bindir = "subdirectory"^squote(bin)

		  val exportflag = SMLofNJ.exportML (bin^"/legoML")

     	  	  fun main (argc,argv) = let 
				       	     val _ = (LEGO (lego_argc, argv) msg legoOS)
			      	 	 in OS.Process.success end

	      in 
	          if exportflag

		     then (LEGO(legoML_argc,[]:string list) msg legoML)

		  else (prnl(); 
		        print("** legoML heap image written in "^bindir^" **");
			prnl(); 
			if b 
	    		   then ()
			else (prnl();
		     	      print("** making lego in "^bindir^" ...");
		     	      prnl();
		     	      SMLofNJ.exportFn((bin^"/lego"),main); 
			      print(" ... done **");
			      prnl()))

	      end 

(* start your engines *)

   	 val _ = (make_lego false "Special FestSchrift edition for Randy Pollack") 

     end; (* make_lego *) 

  end;(* local *)
end; (* struct *)

(* 
structure Main = FunMain
	  (structure Error = Error
	   structure Modules=Modules
	   structure Init=Init
	   structure Pbp=Pbp
	   structure Interface=Interface
	   )
 *)


	   

