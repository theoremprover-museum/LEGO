(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature MODULES =
    sig

	type stamp

(* used in logic.sml *)

	val legoStringParser : (string -> unit) ref

(* used in interface.sml, so needed for toplevel processing *)

	val legoFileParser   : (stamp -> (unit -> unit) -> unit) ref

    	val initStampString      : unit -> stamp
    	val initStampInteractive : unit -> stamp

	val isDepChecking : stamp -> bool

	val getFileName : stamp -> string

        exception DepCheckDone of string list

(* used in lego.grm, so needed for toplevel parsing *)

	val Load : string -> unit
	val Make : string -> unit
	val ReloadFrom  : string -> string -> unit
	val Include : string -> unit

	val ModuleHeader : stamp  -> (string * string list) -> unit

        val SetSaveObjects: bool -> unit

    end;
