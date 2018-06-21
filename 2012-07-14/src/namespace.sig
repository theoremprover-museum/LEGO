(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* 
   $Log: namespace-sig.sml,v $
   Revision 1.6  1998/11/10 15:30:00  ctm
   added interface for adding Labels and searching by corresponding tags

   Revision 1.5  1997/11/24 11:01:36  tms
   merged immed-may-fail with main branch

   Revision 1.4.2.3  1997/10/13 16:47:13  djs
   More problems with the above.

   Revision 1.4.2.2  1997/10/13 16:21:30  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.4.2.1  1997/10/10 17:02:39  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.4  1997/05/08 13:54:59  tms
   Generalised Expansion Mechanism to Cope with Path information
  
   Revision 1.3  1997/03/06 09:54:00  tms
   added mkNameLoc and initNameLoc, previously available in the module pbp
*)

local

in 

  signature NAMESPACE =
    sig

	type cnstr
	type binding 

	type context

	type substitution 

	type Kind
	type Prefix 
	type Frz
	type LocGlob 

	type goal (* = int * cnstr *) (* push into the mix ! *)
  	type goals (* = goal list *) 

      val noMoreGoals : goals -> bool 

      val isSort : cnstr -> bool (* moved from Toc; was "kind" before *)

      val init_namespace : unit -> unit
      val getNamespace   : unit -> context
      val getBindings    : unit -> binding list 
      val topNamespace   : unit -> binding

      val searchNamespace : string -> binding
      val isNewName       : string -> bool

      val mkNameGbl     : string -> string
      (*  mkNameGbl s = s if s is a fresh identifier relative to the context 
          mkNameGbl s = t for a fresh t otherwise *)

      val mkNameLoc     : string -> string
      (* mkNameLoc s = s if (mkNameGbl s = s) and s hasn't been returned
                            previously by mkNameLoc
	 mkNameLoc s = t for a fresh t otherwise
		
         Notice that initNameLoc will effectively undo any previous
         mkNameLoc invocation *)

      val initNameLoc   : unit -> unit
	  
(*****************************************************************)
(* WARNING: These are UNSAFE; putNamespace must not be exported  *)
(*          putNamespace is currently required in newtop.sml     *)
(*	                 discharge.sml, synt.sml and qmaster.sml *)
(*                                                               *)
(*****************************************************************)
      val putNamespace  : context -> unit
      val putBindings   : binding list -> unit
(* 
      val addNamespace  : binding -> unit
 *)
      val NSPWrapper: ('a -> 'b) ->  'a -> 'b

(* needed for qmaster *)

      val addGenGbl : string list -> Frz -> LocGlob -> string list
	-> string -> cnstr * cnstr -> unit

(* needed for newtop *)

      val addBndGbl : Kind -> Prefix 
	-> string -> cnstr * cnstr -> unit

(*    val latestTsGbl   : unit -> int *)

(*    val lclGenCxtGbl  : cnstr * cnstr -> string -> cnstr * cnstr *) 

(*    val dischCxtGbl   : cnstr * cnstr -> (cnstr * cnstr) * binding *)

       datatype question = (* this drives it, but do we need to see it? *)
	Push of int * int * cnstr  (* ??? (n,m,c) is goal (n,c) at timestamp m ??? *)
      | Unknown of goals;

      val getCurrentQuest  : unit -> question list
      val putCurrentQuest  : question list -> unit
      (*******************************************************************)
      (* WARNING: This is UNSAFE; putCurrentQuest should not be exported *)
      (*             putCurrentQuest is currently required in Synt.solve *)
      (*******************************************************************)

      val DECH          : unit -> unit

      val DECHWrapper   : (unit -> unit)  -> (* no more goals  *)
      	  		  (unit -> unit)  -> (* push/discharge state *)
      	  		  (goals -> unit) -> (* process current goals  *)
      	  		   unit -> unit 

      val DischargeKeep : string -> unit
      val Discharge     : string -> unit
      val Forget        : string -> unit

      val addMark       : string*string list*Utils.Timing.time -> unit

      val addConfig     : string*(string*string*string)->unit (* changed 2011 *) 

      val addConfigInfix       : string*bool*int->unit (* changed 2011 *) 
      val addConfigInfixNAssoc : string -> unit (* added 2011 *) 

      val addConfigObjects   : unit->unit
      val addConfigNoObjects : unit->unit

      val findConfig    : string->(string*string*string)->
                                  (string*string*string)

      val addLabel      : string list*string -> unit
      val spotLabel     : string list -> (cnstr*cnstr) option

      val init_history  : unit -> unit
      val pushHist      : unit -> unit
      val tacticalPushHist : unit -> unit
      val QED   : (string * bool) * (cnstr * cnstr) -> unit
      val activeProofState : unit -> bool
      val proofState    : unit -> bool
      val provenState   : unit -> bool
      val no_history    : (unit -> unit) -> unit -> unit
      val undo          : unit -> unit
      val discard       : unit -> unit
      val tactic_wrapper : (unit -> unit) -> unit -> unit

      val getNUN : unit -> int
      val goals : unit -> goals * question list
      val subgoals : unit -> goal * goals * question list

      val unGoal : goal -> int * cnstr
      val unGoals : goals -> goal list

        val current_goal_indexes : unit -> int list
	val current_goal_index   : unit -> int
	val current_goal_type    : unit -> cnstr

	val goalIndex : goal -> int
	val goalType   : goal -> cnstr

	val goaln : int -> goal (*!*)
	val rel_goal_index : bool * int -> int
	val abs_goal_index : int -> int

      val erase_replace : substitution -> int -> goals -> goals -> goals (*!*)
      val eraseq : substitution -> question list -> question list
(*    val erase : substitution -> goals -> goals *)

      val solve : bool -> substitution * int * goals * (unit -> int) * cnstr -> unit 
      val solved : substitution * int * goals * (unit -> int) * cnstr -> bool 

      val manageVars : unit
	-> ((* make new goals, with local gensym *)(cnstr -> cnstr) *
	    (* close generated subgoals wrt sbst *)(substitution -> goals) *
	    (* update the global gensym counter  *)(unit -> int))

(* moved from SYNT; good name? *)

	val type_of_Var : int -> cnstr

(* *************************** *)

      val topContextBeforeProof : unit -> binding 
      val inContextBeforeProof : binding -> bool

(* added from SYNT 2011 only used in Synt.resolve_{a,c} *)

	val subPrfCxt : substitution -> context 

(* *************************** *)

      val getProofTerm : unit -> cnstr
      val putProofTerm : cnstr -> unit
      (*****************************************************************)
      (* WARNING: This is UNSAFE; putProofTerm should not be exported  *)
      (*          putProofTerm is currently required in Synt.solve     *)
      (*****************************************************************)

(* ************************************************************************** *)
(* these get exported to implement Toplevel versions of same: sort names out! *)
(* ************************************************************************** *)

      val Goal    : cnstr -> unit;
      val Claim   : cnstr -> substitution 
	-> ((* make new goals, with local gensym *)(cnstr -> cnstr) *
	    (* close generated subgoals wrt sbst *)(substitution -> goals) *
	    (* update the global gensym counter  *)(unit -> int))
	-> unit

      val Next    : int -> unit
      val Undo 	  : int -> unit
      val UndoAll : unit -> unit
      val KillRef : unit -> unit

      val Save : string -> (Frz * LocGlob) -> unit

      val do_intros : bool * bool -> int -> string list -> int

      val Dnf : unit -> unit
      val Normal : unit -> unit
      val Hnf : unit -> unit
      val Equiv : substitution -> cnstr -> int
      val Expand : int list -> string list -> unit
      val ExpAll : int list -> int -> unit
      val SaveReductGbl : cnstr * cnstr -> unit
      val MakeAllPats : unit -> unit
      val ForgetMrk : string -> unit
      val Freeze : string list -> unit
      val Unfreeze : string list -> unit

      val StartTheory : string -> unit
      val EndTheory : string -> unit

(* ************************************************************************** *)

    end (* sig *)

end; (* local *) 

