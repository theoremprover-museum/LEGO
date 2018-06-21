(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature QUARTERMASTER =
sig

  type cnstr_c

  type binder_c

  val Label : (string list) -> string -> unit
  val Generate : (string list) -> binder_c -> unit
  val GenerateDefn : (string list) -> string -> cnstr_c -> unit
  val GenerateProp : (string list) -> unit
  val Make : (cnstr_c list) -> cnstr_c

  exception quartermaster

  val Register : ((cnstr_c list) -> (cnstr_c * bool)) -> unit
  val SLtoCL : (string list) -> (cnstr_c list)
  val CLtoSLo : (cnstr_c list) -> (string list) option

end

