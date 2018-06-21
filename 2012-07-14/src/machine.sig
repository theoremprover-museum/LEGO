(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature MACHINE =

  sig

	type cnstr
	type binding
	type context
	type substitution

	type Kind 
	type Prefix 
	type projSort 
	type prntVisSort 

(* 
    val kind : cnstr -> bool		(* moved to Namespace *)
    val coerceGe : cnstr -> cnstr	(* moved to Machine *)
 *)

    val addNewBnd : Kind -> Prefix -> string -> (cnstr * cnstr) -> context -> context

    val mkBndFresh : Kind -> Prefix -> string -> (cnstr * cnstr) -> context -> binding

    val addBndFresh : Kind -> Prefix -> string -> (cnstr * cnstr) -> context -> context

    val ConsiderNam : string -> context -> cnstr * cnstr
    val ConsiderVar :    int ->   cnstr -> cnstr * cnstr

    val ConsiderTerm :  cnstr -> cnstr * cnstr (* encapsulates Toc.toc *)

    val Projection : projSort -> cnstr * cnstr -> cnstr * cnstr
(* 
    val ProjectTheory : string -> cnstr * cnstr -> cnstr * cnstr (* in Toc *)
 *)
    val tuplize 
      : substitution 
      -> cnstr -> (cnstr * cnstr) list 
      -> (cnstr * cnstr) * substitution 

    val Apply 
      : substitution 
      -> (cnstr -> cnstr)
      -> prntVisSort
      -> cnstr * cnstr
      -> cnstr * cnstr -> (cnstr * cnstr) * substitution 

    val ConsiderType   : string -> cnstr * cnstr
    val ConsiderTypen  : int    -> cnstr * cnstr
    val ConsiderProp   : unit   -> cnstr * cnstr
    val ConsiderTheory : unit   -> cnstr * cnstr

    val letize     : cnstr * cnstr -> binding -> cnstr * cnstr
    val abstract   : cnstr * cnstr -> binding -> cnstr * cnstr
    val generalize : cnstr * cnstr -> binding -> cnstr * cnstr
    val sigize     : cnstr * cnstr -> binding -> cnstr * cnstr

    val dischCxt   : cnstr * cnstr -> context
		   	 -> (cnstr * cnstr) * binding * context

    val lclGenCxt  : cnstr * cnstr -> string -> context -> cnstr * cnstr

  end
