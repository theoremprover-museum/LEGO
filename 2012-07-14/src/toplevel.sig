(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

  signature TOPLEVEL =
    sig
	type cnstr_c

(* 
	exception Solve
 *)
	val init_toplevel : unit -> unit

	val Pr : unit -> unit
	val PR : unit -> unit
	val prAnnotating : unit -> unit (* *** only one to export? *** *)

(* for Conor in OLEG *)

	val legoGoalName : unit -> string  

(* 2011 LocGlob flag to Goal/Save/SaveDefault becomes a boolean *)

	val Goal    : cnstr_c -> string * bool -> unit
	val Intros  : bool -> int -> string list -> unit
	val Refine  : int -> int -> cnstr_c -> unit
	val Immed   : unit -> unit
	val Assumption : int -> unit

     (* Refine* n m v_c refines goal n with v_c applied to m explicit metavars *)

	val Claim   : cnstr_c -> unit

	val Next    : int -> unit
	val Undo    : int -> unit
	val UndoAll : unit -> unit
	val KillRef : unit -> unit

  	val Save    : bool -> string -> unit

  	val SaveDefault : string * bool -> unit
	val ConfigSaveFroz : unit -> unit 
	val ConfigSaveUnFroz : unit -> unit

	val AppTac : ('a -> 'b) -> 'a -> unit
	val smallAppTac : ('a -> 'b) -> 'a -> unit

(* *** 2011: removed from the signature, as no longer used anywhere *** *
	type autotac (* mad now *)
	val mkAuto : (goals -> unit) -> autotac 
(* 
	val unAuto : autotac -> goals -> unit 
 *)
	val nullTac : autotac
	val getAutoTac : unit -> autotac 
	val setAutoTac : autotac -> unit
(* 
	val SolveImmed      : int -> int -> cnstr_c -> bool
 *)

	val RefineRaise_c   : int -> int -> cnstr_c -> unit (* can raise Solve *)

 * ***                                                              *** *)

(* needed in Logic *)
	val RefineHandle_c   : int -> int -> cnstr_c ->     (* this handles it *)
	    		       	     	    (cnstr_c -> unit) -> unit

	val RefineTac_c     : int -> int -> cnstr_c -> unit

	val IntrosTac : bool -> int -> string list -> int 

(* *** 2011: removed from the signature, as no longer used anywhere *** *
	val RefineAutoTac_c : int -> int -> cnstr_c -> unit
	val RefineWithTac_c : int -> int -> cnstr_c -> 
	    		       	     	    autotac -> unit
	val RefineWith      : int -> int -> cnstr_c -> 
	    		       	     	    autotac -> unit
 * ***                                                              *** *)


    end
