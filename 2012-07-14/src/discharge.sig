(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature DISCHARGE =
    sig
	type cnstr_c
	val Cut : (string * cnstr_c) list -> unit
    end;
