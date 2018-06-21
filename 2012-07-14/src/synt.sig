(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

local

in 

signature SYNT =
    sig
	type cnstr

	type cnstr_c

	type autotac 

	exception Solve (* "doesn't solve goal" *)

	val nullTac : autotac 

	(* canNOT raise Solve: true if it succeeds with no new subgoals; o/w false *)
	val SolveImmed : int -> int -> cnstr_c -> bool

	(* can raise Solve *)
	val Solve_c    : bool -> int -> int -> cnstr_c -> autotac -> unit
	val Solve_a    : bool -> int -> int -> cnstr   -> autotac -> unit

	(* 2011: go via Namespace-only solve/solved *)
	val SolveImmed_s : int -> int -> cnstr_c -> bool
	val Solve_s      : bool -> int -> int -> cnstr_c -> unit
    end

end; (* local *)

