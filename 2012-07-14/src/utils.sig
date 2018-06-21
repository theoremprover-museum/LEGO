(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature UTILS = 
  sig

   val UNSAFEeq : 'a * 'a -> bool; 

   structure Except : 
    sig 
    exception Failure of string
    val failwith : string -> 'a
    exception Bug of string
    val bug : string -> 'a

    val try_raise_finally : ('a -> 'b) -> ('b -> 'c) -> ('b -> 'd) -> 'a -> 'c
                           (* opening *) (* doing *)  (* finalising *)
    end; 

  structure Modif : 
    sig 
    datatype 'a modif = Mod of 'a | UMod

    val share  : ('a -> 'a modif) -> 'a -> 'a
    val share2 : ('a -> 'a modif) * ('b -> 'b modif)
                 -> 'a * 'b -> ('a * 'b) modif
    val share2f   : ('a -> 'a modif) -> 'a * 'a -> ('a * 'a) modif
    val map_share : ('a -> 'a modif) -> 'a list -> 'a list modif

    val post_share : ('a -> 'b modif) -> 'a -> ('b -> 'c) -> 'c -> 'c
    end; 

  structure Counting : 
    sig 
    val succ : int -> int
    val pred : int -> int

    val counter : int -> unit -> int (* for gensym *)
    val Counter : int -> (unit -> unit)*(unit -> unit)*(unit -> int) 
    		      	   (* init *)	  (* tick *)	 (* read *)

    end; 

  structure ListUtil : 
    sig 
(* ******************************************************** * 
(* 	2011 removed: more list primitives		    *)

    val do_list : ('a -> 'b) -> 'a list -> unit

    exception Empty of string
    val last : 'a list -> 'a
    val dropLast : 'a list -> 'a list
    val removeLast : 'a list -> 'a * 'a list

    val foldr : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b

    val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a

    val foldr1 : ('a -> 'a -> 'a) -> 'a list -> 'a

    val filter_split : ('a -> bool) -> 'a list -> 'a list * 'a list
 * ******************************************************** *)

    val filter_pos : ('a -> bool) -> 'a list -> 'a list
    val filter_neg : ('a -> bool) -> 'a list -> 'a list

    exception Nth of int
    val nth : 'a list -> int -> 'a
    val first_n : int -> 'a list -> 'a list

    val member : ''a -> ''a list -> bool
    val add_if_missing : ''a -> ''a list -> ''a list
    val diff : ''a list -> ''a list -> ''a list

    val mem_assoc : ''a -> (''a * 'b) list -> bool
    exception Assoc
    val ASSOC : ''a -> (''a * 'b) list -> ''a * 'b
    val assoc : ''a -> (''a * 'b) list -> 'b
    val prune : ''a -> (''a * 'b) list -> (''a * 'b) list 

    end; 

  structure StringUtil : 
    sig 
    val   nullString : string
    val isNullString : string -> bool
    val wildcard_    : bool -> string -> string 
    val wildcard     : string -> string 

    val isWILDCARD   : string -> bool

    val WILDCARD    : string
    val HYPNAME     : string
    val ZZZNAME     : string
    val spaceString : string
    val spaceChar   : char
    val spaces : int -> string
    val concat_sep : string -> string list -> string
    val concat_space : string list -> string
    val concat_comma : string list -> string

    val squote : string -> string
    val dquote : string -> string

    val legocomment : string -> string

    val fresh : (string -> bool) -> (string -> bool) -> 
    	      		string -> string list -> string 

    val fresh_push : (string -> bool) -> (string -> bool) -> 
    	      		string -> string list -> string * string list

    end; 

  structure Timing : 
    sig 
    type timer 
    type time 
    val start_timer : unit -> timer
    val print_timer : timer -> string
    val check_timer : timer -> {sys:time, usr:time}
    val mks_time : time -> string
    val sub_time : time * time -> time
    val earlier : time * time -> bool
    val makestring_timer : timer -> string

    val timer_wrapper : ('a -> 'b) -> 'a -> 'b * string   
    end; 

  structure FunUtil : 
    sig 
    val repeat : int -> ('a -> 'b) -> 'a -> unit
    val Repeat : int -> ('a -> 'a) -> 'a -> 'a
    exception UntilExn
    val Until : ('a -> 'a) -> 'a -> 'a

    val diag_fun : 'a -> 'a * 'a
    val pair_fun_apply : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
    val pair_apply : ('a -> 'b) -> 'a * 'a -> 'b * 'b
    end; 

  end
