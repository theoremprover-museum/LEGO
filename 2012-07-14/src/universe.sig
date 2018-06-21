(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature UNIVERSES = 
sig

	exception Universes of string

	type node 
	type univ_graph

    val UVARS : univ_graph ref

    val node_equal : node -> node -> bool
    val univ_equal : node -> node -> bool
    val univ_leq   : node -> node -> bool
    val univ_cmp_  : bool -> node -> node -> bool
    val univ_cmp   : node -> node -> bool
	

    val mkNod      : (node -> 'a) -> 'a  -> 'a -> 'a -> (node -> 'a)
    val mkUcon     : int -> node
    val mkUvar	   : string -> node
    val mkUvarGt   : node -> node
    val mkUvarGe   : node -> node -> node

    val tocNode	   : node -> node

    val init_universes 	: unit -> unit
    val tryUniverses   	: ('a -> bool) -> 'a -> bool
    val handleUniverses : ('a -> 'b) -> 'a -> 'b

    val clean_universes : unit -> unit

    val nodeCase : 'a -> (string -> 'a) -> (int -> 'a) -> node -> 'a

end; 

signature THEORIES = 
sig

    val LuosMode  : bool ref 
    val TypeType  : bool ref 
    val AczelMode : bool ref 

    val PredicativeSums   : bool -> unit
    val TypeInType 	  : unit -> unit
    val TypesStratified   : unit -> unit

    datatype theories = lf | pureCC | xtndCC (* systemU also? *)

    val set_inference : theories * bool -> unit
    val theory 	      : 'a -> theories
    val eta 	      : 'a -> bool

    val ThytoString  : unit -> string

    val LF 	: theories * bool
    val LF_no_n : theories * bool
    val PCC 	: theories * bool
    val PCC_n 	: theories * bool
    val XCC 	: theories * bool
    val XCC_n 	: theories * bool

    val init_theories 	: unit -> unit
end; 
 