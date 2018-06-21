(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* init.sml *)
(* Author: Randy Pollack <pollack@cs.chalmers.se> *)

(* CHANGES

   Thomas Schreiber <tms@lfcs.ed.ac.uk>
   February 1995
   Bernhard Reus <reus@informatik.uni-muenchen.de> and
   Peter Aczel <petera@cs.man.ac.uk> prefer small impredicative sigma
   types. To incorporate this extension, I have extended the switch
   ``Init'' *)

functor FunInit (
	structure Infix:INFIX
        structure UMopen:UMOPEN 
        structure Namespace:NAMESPACE
	structure Tactics:TACTICS
	structure Toplevel:TOPLEVEL
	structure Top:TOP
	structure ConorThen:CONORTHEN
(*
	sharing 
	 	 type Tactics.cnstr_c 
	            = Toplevel.cnstr_c 
	and 
	 	 type UMopen.cnstr 
	            = Namespace.cnstr 
	and 
	 	 type Tactics.tactic 
	            = ConorThen.tactic 
 *)
	) 
(* *** * 
structure Init 
* *** *)
	: INIT 
 = 
  
struct
    (* initialization function is defined last *)

    local

      val message = Printing.message 

      val failwith = Utils.Except.failwith 

      fun Init x  =
	(Theories.set_inference x;   (* universe.sml *) 
	 Universes.init_universes(); (* universe.sml *)
	 UMopen.init_reductions();
         Infix.init_infix();
	 Namespace.init_namespace();
	 Toplevel.init_toplevel();
	 Top.init_newtop();
	 ConorThen.InitConorThen();
	 Tactics.init_tactics(); 
	 Tactics.Config_Qrepl("","","");   (* init Qrepl to leibniz equality *)
	 Theories.init_theories());

      fun err() = failwith"MacroMode no longer supported"
    in 

      fun InitLF  () = Init Theories.LF
      fun InitPCC () = Init Theories.PCC
      fun InitXCC () = Init Theories.XCC

      fun Init_raw "LF"     = InitLF ()
	| Init_raw "PCC"    = InitPCC ()
	| Init_raw "XCC"    = (InitXCC (); 
	  	   	       Theories.TypesStratified(); 
			       Theories.PredicativeSums true)
	| Init_raw "XCC'"   = err()
	| Init_raw "XCC_s"  = (InitXCC (); 
	  	   	       Theories.TypesStratified(); 
			       Theories.PredicativeSums false)
	| Init_raw "XCC'_s" = err()
	| Init_raw "U" 	    = (InitXCC (); 
	  	   	       Theories.TypeInType())
	| Init_raw _        = failwith "LF, PCC, XCC or XCC_s expected"

    end

end; 
