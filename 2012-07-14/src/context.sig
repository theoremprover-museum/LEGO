(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature CONTEXT = 
sig	  

	type cnstr (* = Term.cnstr *)
	type binding (* = Term.binding *)
(* *) 	  
	type context

	  val mkCxt : binding list -> context
	  val unCxt : context -> binding list 

	  val emptyCxt : context
	  val isEmptyCxt : context -> bool 
	  
 	  val addBndCxt : binding -> context -> context
    	  val popCxt : context -> binding * context
    	  val topCxt : context -> binding

	  val takeCxt : int -> context -> binding list

	  val init_context : unit -> context

	  val do_cxt_dpth : (binding -> unit) -> int -> context -> unit
	  val do_cxt	  : (binding -> unit) -> context -> unit
	  val do_cxt_ref  : binding -> (binding -> unit) -> context -> unit
	  val do_cxt_nam  : string -> (binding -> unit) -> context -> unit

	  val searchCxt : string -> context -> binding
	  val unDefined : string -> context -> bool

	  val mkLabelBnd : string list * string -> binding
  	  val addLabelCxt : string list * string -> context -> context 
  	  val findLabelCxt : string list -> context -> (cnstr * cnstr) option
 
	  val mkThryBnd : string -> binding
	  val addThryCxt : string -> context -> context

  	  val mkConfigBnd : string * (string * string * string) -> binding
  	  val addConfigCxt : string * (string * string * string)
                     	     	    -> context -> context
  	  val findConfigCxt : string -> string * string * string
                              	     -> context -> string * string * string

          val mkMarkBnd : string * string list * Utils.Timing.time -> binding
  	  val addMarkCxt : string * string list * Utils.Timing.time
                   	   	  -> context -> context

	  val mkReductBnd : cnstr * cnstr -> binding
	  val addReductCxt : cnstr * cnstr -> context -> context

	  val FreezeCxt   : string list -> context -> unit
	  val UnfreezeCxt : string list -> context -> unit

	  val splitCxt : (binding -> bool) -> string 
	      	            -> context -> binding * context * context


end; 
