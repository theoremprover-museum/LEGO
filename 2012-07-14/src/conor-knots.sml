(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature CONORKNOTTYPES =
sig
  eqtype knot
  type entry

  val doIt : entry -> unit  
  val isIt : knot -> (knot -> bool) (* eqtype knot! *)
end

structure PromptKnotTypes :CONORKNOTTYPES =
struct
  type knot = string
  type entry = unit -> unit

  fun doIt f = f ()

  fun isIt (k:knot) = fn x => x=k

  val (Then:knot) = "ConorThen"
end

structure UndoKnotTypes   :CONORKNOTTYPES =
struct
  type knot = string
  type entry = unit -> unit

  fun doIt f = f ()

  fun isIt (k:knot) = fn x => x=k

  val (Init:knot) = "Init"
  val (Mark:knot) = "Mark"
  val (Undo:knot) = "Undo"
  val (Discard:knot) = "Discard"
end

signature CONORKNOTS =
sig
  structure KT : CONORKNOTTYPES
  exception no_such_knot
  val do_all_knots      : (KT.knot -> bool) -> unit
  val tie_knot          : KT.entry -> KT.knot -> unit
  val tie_knots         : KT.entry -> KT.knot list -> unit
  val seek_first_knot   :  KT.knot -> KT.entry
  val seek_one_knot     : (KT.knot -> bool) -> KT.entry
  val seek_all_knots    : (KT.knot -> bool) -> KT.entry list
  val remove_one_knot   : (KT.knot -> bool) -> unit
  val remove_all_knots  : (KT.knot -> bool) -> unit
  val init_knots    : unit -> unit
  val push_knots    : unit -> unit
  val undo_knots    : int -> unit
  val discard_knots : int -> unit
end

functor FunConorKnots(KT':CONORKNOTTYPES) : (* CONORKNOTS = *)

					    sig
					       include CONORKNOTS
					       where KT = KT'
					    end 
   = 

struct
  structure KT = KT'
  exception no_such_knot
  local

(*  val (hanky : (KT.knot * KT.entry) list ref) = ref [] *)
    val hanky = ref ([] : (KT.knot * KT.entry) list)
    val hanky_chain = ref [(!hanky)]

  in

    fun tie_knots ent =
	let
	    fun tk2 []     = ()
	      | tk2 (h::t) = ((hanky := (h,ent)::(!hanky));
                              (tk2 t))
	in
	    tk2
	end

    fun tie_knot ent k = tie_knots ent [k]

    fun remove_one_knot knot =
	let
	    fun rk2 [] = raise no_such_knot
	      | rk2 ((h as (hk,_))::t) =
		if (knot hk) then (t)
		else h::(rk2 t)
	in
	    hanky := rk2 (!hanky)
	end

    fun remove_all_knots knot =
	((remove_one_knot knot);
         (remove_all_knots knot))
	handle no_such_knot => ()

    fun seek_one_knot k =
	let
	    fun sok2 []           = raise no_such_knot
	      | sok2 ((hk,ht)::t) = if (k hk) then ht else sok2 t
	in
	    sok2 (!hanky)
	end

    fun seek_first_knot k = let 
    			    	val p = KT.isIt k
    			    	val e = seek_one_knot p
				val _ = remove_all_knots p
			    in 
				e
			    end 

    fun seek_all_knots k =
	let
	    fun sak2 []           = []
	      | sak2 ((hk,ht)::t) = if (k hk) then ht::(sak2 t)
                                    else sak2 t
	in
	    sak2 (!hanky)
	end

    fun do_all_knots k = (List.map KT.doIt (seek_all_knots k); ())

    fun init_knots () = remove_all_knots (fn _ => true) 

    fun push_knots () = hanky_chain := (!hanky)::(!hanky_chain)

    fun undo_knots 0 = ()
      | undo_knots n = (((fn [] => ()
			 | (h::t) => ((hanky := h);(hanky_chain := t)))
	               (!hanky_chain));(undo_knots (n-1)))

    fun discard_knots 0 = ()
      | discard_knots n = (((fn [] => ()
                            | (h::t) => (hanky_chain := t))
	                  (!hanky_chain));(discard_knots (n-1)))
  end
end
