(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature INIT =
    sig
	val Init_raw : string -> unit
	val InitLF   : unit -> unit
	val InitPCC  : unit -> unit
	val InitXCC  : unit -> unit
    end;
