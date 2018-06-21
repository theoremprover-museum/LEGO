(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* *** Save doesn't save any deps: why not? JHM 2009.12.08 *** *)

(* 
   $Log: namespace.sml,v $
   Revision 1.14  1998/11/10 15:30:48  ctm
   added code for adding Labels and searching by corresponding tags;
   modified Discharge to cope with `Generate' and `Label'

   Revision 1.13  1998/10/30 14:15:55  ctm
   discharge modified to take visibility from resulting abstractions etc,
   rather than the initial binding---allowing for conditional visibility

   Revision 1.12  1998/10/28 16:01:45  ctm
   Modified discharge so parameter visibilities are chosen according to
   argument type dependency; eg list and nil have visible type arg while
   cons and list_elim suppress it.

   Revision 1.11  1998/10/23 13:50:52  tms
   "Forget id" now also reports on retraction across module boundaries.
   This is required for the Emacs interface Proof General

   Revision 1.10  1998/10/18 11:35:50  tms
   Function forget now prints out a loud message. This makes it easier
   for an interface such as Proof General to recognise that LEGO has
   retracted across file boundaries.

   Revision 1.9  1997/11/24 11:01:39  tms
   merged immed-may-fail with main branch

   Revision 1.8.2.2  1997/10/13 16:21:33  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.

   Revision 1.8.2.1  1997/10/10 17:02:41  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.8  1997/05/08 13:55:07  tms
   Generalised Expansion Mechanism to Cope with Path information
  
   Revision 1.7  1997/03/06 09:54:09  tms
   added mkNameLoc and initNameLoc, previously available in the module pbp
*)

functor FunNamespace(structure Term : TERM 
		     structure Context:CONTEXT
		     structure Subst : SUBST 
		     structure UMopen : UMOPEN 
		     structure Expand: EXPAND
		     structure ParTm : PARTM
		     structure UndoKnots:sig  
 				           include CONORKNOTS  
 				           where KT = UndoKnotTypes    
 			                 end
		     structure Machine:MACHINE
		     structure Pretty:PRETTY
		     sharing 
		     	     type Term.cnstr
			      	= Context.cnstr
			      	= Subst.cnstr
			      	= UMopen.cnstr
			      	= Expand.cnstr
			      	= ParTm.cnstr
			      	= Machine.cnstr
			      	= Pretty.cnstr
		     and 
		   	   type Subst.substitution
			      = ParTm.substitution
		     and 
		   	   type Term.binding
			      = Context.binding
			      = Subst.binding
			      = Machine.binding
			      = Pretty.binding
		     and 
		   	   type Context.context
			      = Machine.context
			      = Pretty.context
		     and 
		   	   type Term.Kind
			      = Machine.Kind
		     and 
		   	   type Term.Prefix
			      = Machine.Prefix
		     and 
		   	   type Term.projSort
			      = Machine.projSort
		     and 
		   	   type Term.prntVisSort
			      = Machine.prntVisSort
		     )
(* *** * 
structure Namespace
 * *** *)
        : NAMESPACE 

 =

struct

	type cnstr = Term.cnstr
	type binding = Term.binding

	type context = Context.context 

	type substitution = Subst.substitution 

  	type goal = int * cnstr
  	type goals = goal list

	fun unGoal g = g
	fun unGoals gs = gs

	type Kind = Term.Kind 
	type Prefix = Term.Prefix 
	type LocGlob = Term.LocGlob 
	type Frz = Term.Frz

local

	val prs = Printing.prs
	val prnl = Printing.prnl
	val message = Printing.message
	val loudmessage = Printing.loudmessage

        val dnf  = UMopen.UMdnf
        val whnf = UMopen.UMwhnf
(* 
	val dom = Subst.dom
	val sub = Subst.sub
	val mkSubst1 = Subst.mkSubst1
	val subst1 = Subst.subst1
	val subRef_pr = Subst.subRef_pr 
 *)
	val par_unif = ParTm.par_unif

	open Utils.Except 
	open Utils.Counting 
	open Utils.Timing 
	open Utils.ListUtil 
	open Utils.StringUtil 
	open Utils.FunUtil 
	open Utils.Modif 
	open Term 
	open Context
	open Subst  

in 

   fun isSort T = isKind (whnf T); (* isKind in Term now *)

  (* ******************************************************************** *)

  (* 		what this is all about	(JHM, 2009-11-11)		  *)

  (* ******************************************************************** *
     
     NSP is the Context: the basic list-based finite map on top of which 
     type-checking takes place
     
     UVARS is the universe dependency graph, defined in universes.sml
     
     HIST is a general history stack for proofs (with some delicate issues 
     as to undoing tactics)
     
     QUEST is the goal stack for a given proof
     
     NUN is a counter for numbering metavariables on a per-proof basis
     
     COM is the current partially instantiated proof object
     
     LNSP is a stack of fresh names locally defined on a per-proof basis
     
   * ******************************************************************** *)

(******************************************************)
(* WARNING: These are UNSAFE;                         *)
(*          putNSP is currently required in synt.sml  *)
(*          	      		       discharge.sml  *)
(*          addNSP      	     	 qmaster.sml  *)
(******************************************************)

   val NSP = ref(emptyCxt)

   fun init_namespace() = NSP:= init_context ();

   fun getNamespace() =  (!NSP)
   fun topNamespace() = topCxt (getNamespace())

   fun getBindings() =  Context.unCxt (getNamespace())

   fun putNamespace nsp  = (NSP := nsp)
   fun putBindings brs =  putNamespace(Context.mkCxt brs)

   fun addNamespace bnd  = putNamespace(addBndCxt bnd (getNamespace()))

   fun NSPWrapper f x = let
			   val nsp = getNamespace()
			   val y = (f x handle e => (putNamespace nsp; raise e))
			in 
			   y
			end; 

   (* Return the latest timestamp in the Global context *)
   fun latestTsGbl() = ref_ts (topNamespace());

   (* Interrogate the namespace *)
   fun searchNamespace nam = searchCxt nam (getNamespace())
		
   fun isNewName nam = unDefined nam (getNamespace())

   (* make a name not occurring in the global context *)
   fun mkNameGbl nam = 
       let fun mnrec m =
       	   let val nn = nam^Int.toString m
      	    in if isNewName nn then nn else mnrec (succ m) 
	   end
    	in if isNewName nam then nam else mnrec 1
       end;

   (* local namespace with constructors initNameLoc and mkNameLoc *)
   local

	val LNSP = ref ([]:string list)

   in 

   (* initialise local namespace *)
   fun initNameLoc () = LNSP := []

   (* make a name neither occurring in the global nor in the local namespace *)
   fun mkNameLoc (s:string) =
      let
	  fun new_name () = 
	      let val real_name = mkNameGbl s
	      in
		  if (member real_name (!LNSP)) then
		      let fun new_name_aux n  =
			  let val cur_s = (s ^ (Int.toString n))
			      val cur_real_name = mkNameGbl cur_s in
				  if member cur_real_name (!LNSP) then
				      new_name_aux (succ n) 
				  else 
				      cur_real_name
			  end
		      in 
			  new_name_aux 0 
		      end
		  else real_name
	      end
	  val new_id = new_name()
      in
	  LNSP := new_id::(!LNSP); new_id
      end

    end; 

(* ********************************************************************** *) 

(* context management *) (* expand namespace: refactored via Machine *)

(* new: consider moving mkBndFresh to Machine? no: EndTheory needs it here *)

(* 2011: moved mkBndFresh to Machine; use workaround addThyGbl for EndTheory *)

(* *** *
  fun mkThyGbl nam thry cxt = 
      Machine.mkBndFresh Bnd (Prefix(Let,Def,UnFroz,Global,[])) nam (thry,Theory) cxt  

  fun mkGenGbl tag (frz_par_flg as (fr,lg)) deps = 
      mkBndGbl (GenTag tag) (Prefix(Let,Def,fr,lg,deps)) 

  fun addBndGbl K pfx n tk = (* replaces extendCxtGbl: result type *)
      putNamespace (Machine.addBndFresh K pfx n tk (getNamespace()))

  fun addLdaGbl vis = 
      addBndGbl Bnd (Prefix(Lda,vis,UnFroz,Local,[])) 

  fun addLetGbl vis = 
      addBndGbl Bnd (Prefix(Let,vis,UnFroz,Local,[])) 

 * *** *)

  fun mkBndGbl K pfx n (tk) =
      Machine.mkBndFresh K pfx n tk (getNamespace())

  fun mkLdaGbl vis = 
      mkBndGbl Bnd (Prefix(Lda,vis,UnFroz,Local,[])) 

  fun mkLetGbl vis = 
      mkBndGbl Bnd (Prefix(Let,vis,UnFroz,Local,[])) 

  fun addBndGbl K pfx n tk = (* replaces extendCxtGbl: result type *)
      addNamespace (mkBndGbl K pfx n tk)

  fun addGenGbl tag fr lg deps = 
      addBndGbl (GenTag tag) (Prefix(Let,Def,fr,lg,deps)) 

  fun addThyGbl nam thry cxt = 
      Machine.addBndFresh Bnd (Prefix(Let,Def,UnFroz,Global,[])) nam (thry,Theory) cxt  


(* ******************************************************************* *)
  (* la preuve partielle *)
  val COM = ref Bot;
  fun getProofTerm() = (!COM)
  fun putProofTerm t = (COM := t)

  (* reference to newest context before proof *)
  val GOAL_CTXT = ref (!NSP);
  fun getContextBeforeProof() = (!GOAL_CTXT)
  fun putContextBeforeProof nsp = (GOAL_CTXT:= nsp)
  fun topContextBeforeProof() = topCxt (!GOAL_CTXT) (* ? *)

  fun inContextBeforeProof br = sameRef br (topContextBeforeProof())

  (* Return the latest timestamp in the Global context *)
  fun latestTsLoc() = ref_ts (topContextBeforeProof());

  (* for SYNT: refactor again? *)
(* 2011: context or binding list when it comes to iteration? *
  fun subPrfCxt_ s (nsp as (b::l)) =
        if (inContextBeforeProof b) then nsp
       else ref_updat_vt b (pair_apply (sub s) (ref_vt b))::(subPrfCxt_ s l)
    | subPrfCxt_ s [] = bug"subPrfCxt"
 *)
  fun subPrfCxt_ s nsp = 
      if isEmptyCxt nsp then bug"subPrfCxt"
      else let 
      	       val (b,l) = Context.popCxt nsp
      	   in 
	      if (inContextBeforeProof b) then nsp 
	      else Context.addBndCxt 
	      	   (ref_updat_vt b (pair_apply (sub s) (ref_vt b))) 
		   (subPrfCxt_ s l)
	   end 

  fun subPrfCxt s = subPrfCxt_ s (getNamespace())

(* ******************************************************************* *)
  (* "quest" is the type of the current goals.
   * Empty is the null list of subgoals.
   * Push indicates introductions, hence a change of context.
   *    When Push is the head of a "quest", a discharge is
   *    needed, after Push is removed so previous goals are
   *    restored in their correct context.
   * Unknown is the list of subgoals in the current context.
   *)

  datatype question =
    Push of int * int * cnstr
  | Unknown of goals;

  val noMoreGoals = List.null 

  type quest = question list;

  val QUEST = ref([] : quest);
  fun getCurrentQuest() = (!QUEST)
  fun putCurrentQuest qs = QUEST := qs

  fun type_of_Var n = 
    let fun tov_rec (Unknown(l)::q) = ((assoc n l) handle _ =>  (tov_rec q))
          | tov_rec (_::q) = tov_rec q
          | tov_rec [] = failwith("Undefined metavar: ?"^(Int.toString n))
    in  tov_rec (!QUEST) 
    end;

(* *** metavariables: generators, erasers, history updaters *** *)

   local
     fun ff s (g as (m,c),gs) = if dom m s then gs else (m, sub s c)::gs
   in
     fun erase s gs = List.foldr (ff s) ([]) gs (* 2011: List.foldr *)
     fun erase_replace s n new = (* 2011: List.foldr *)
       let fun fff (gs as ((m,c),l)) = if n=m then new@l else ff s gs
       in  List.foldr fff []
       end
   end;

   local 
     fun map_quest fU fc =
      List.map (fn Unknown(l) => Unknown(fU l) | Push(n,m,c) => Push(n,m,fc c))
   in 
     fun eraseq s (qs:question list) = map_quest (erase s) (sub s) qs
   end 
(*
  fun eraseq s =
    let fun map_quest fU fc =
      List.map (fn Unknown(l) => Unknown(fU l) | Push(n,m,c) => Push(n,m,fc c))
    in  map_quest (erase s) (sub s)
    end
*)

   (* for gensym *)
  val NUN = ref(0);

  fun getNUN () = !NUN (* we can work out if tacs create new goals this way *)

   (* some tools for managing metavars *)
  fun manageVars() =
    let 
      val nun = ref(!NUN)
      val newVars = ref([] : goals)
      fun mkNewVars cc = 
	let val nc = ((nun:= !nun+1; !nun),cc) 
	in (newVars:= !newVars@[nc]; Var(nc))
	end
      fun eraseNewVars t = 
	(newVars:= List.map (fn (n,c) => (n,dnf c)) (erase t (!newVars)); (* dnf *)
	 !newVars)
      fun closeNewVars() = (NUN:= !nun; !NUN)
    in  (mkNewVars,eraseNewVars,closeNewVars)
    end;

(* ******************************************************************* *)
(* Discharge *)

(* ye olde version ***************************************************** *)

(* moved to Machine *
fun dischCxt VT =
  let
    fun preDischCxt br =
      case ref_bind br
	of Let => Machine.letize VT br
	 | Lda => Machine.abstract VT br
	 | Pi  => Machine.generalize VT br
	 | Sig => Machine.sigize VT br
	 | Thry => bug"dischCxt"
  in
    fn  b::bs  => (preDischCxt b,b,bs)
     |   []    => failwith"cannot discharge; context empty"
  end
 * **************** *)


fun DECHWrapper_ qed dech_push dech_pop process_goals () = 
    case (!QUEST) 
      of      	    [] 	 => qed () 
       | Push(n,m,c)::q  => dech_push (n,m,c) q
       | Unknown([])::q  => dech_pop q
       | Unknown(gs)::_  => process_goals gs 

fun DECHWrapper qed dech process_goals () = 
(* 
    let 
    	fun dech_push (n,m,c) q = dech ()
    	fun dech_pop q = dech ()
    in  
    	DECHWrapper_ qed dech_push dech_pop process_goals ()
    end 
 *)
    case (!QUEST) 
      of      	    [] 	 => qed () 
       | Push(n,m,c)::q  => dech ()
       | Unknown([])::q  => dech ()
       | Unknown(gs)::_  => process_goals gs 

fun DECH() =
  let 
    fun dischCxtGbl VT = 
    	let val (vt,b,bs) = Machine.dischCxt VT (!NSP)
	in  (NSP:= bs; (vt,b))
	end

    fun disCom m (VT as (V0,_)) =
      let
	fun dc (VT as (V1,_)) =
	  if (m<>latestTsGbl())
	    then let val (dVT,br) = dischCxtGbl VT
		 in  (prs(" "^ref_nam br); dc dVT) 
		 end
	  else V1 (*fst VT*)
      in 
	if (m<>latestTsGbl())
	  then (prs "Discharge.. "; let val dV = dc VT in prnl(); dV end)
	else V0 (*fst VT*)
      end
(* 
    fun qed () = (COM:= disCom (latestTsLoc()) (Machine.ConsiderTerm (!COM)))

    fun dech_pop q = (QUEST := q)

    fun dech_push (n,m,c) q = 
    	let 
	    val dis = disCom m (Machine.ConsiderTerm (!COM))
	    val sbst = mkSubst1(n,dis)
	in (COM := sub sbst c; 
	    QUEST := eraseq sbst q) 
	end

    fun process_goals gs =  bug "Namespace.DECH"
 *)
  in
(* 
	DECHWrapper_ qed dech_push dech_pop process_goals ()
 *)			 
    case (!QUEST) of
      Unknown([])::q => QUEST := q
    | Push(n,m,c)::q =>
	let val dis = disCom m (Machine.ConsiderTerm (!COM))
	    val sbst = mkSubst1(n,dis)
	in (COM := sub sbst c; 
	    QUEST := eraseq sbst q) 
	end
    | [] => COM:= disCom (latestTsLoc()) (Machine.ConsiderTerm (!COM))
    |  _ => bug "Namespace.DECH" 
  end
				 
(* ******************************************************************* *)
  (* history; for UNDO *)
  datatype hist = Initial  | NoProof
  | State of state
  | Proven of ((string*LocGlob) * (cnstr*cnstr)) * hist

  withtype state = 		(* put univ_graph separately? *) 
    cnstr * quest * int * context * Universes.univ_graph * hist; 

  val HIST = ref NoProof;

  fun proofState()  = case !HIST of NoProof => false | _ => true

  fun activeProofState() =
     case !HIST of Initial => true | State s => true | _ => false

  fun provenState() = case !HIST of Proven s => true | _ => false;

  fun proven nvt = HIST:= Proven(nvt,!HIST)

  fun QED ((n,b),vt) = proven ((n,mkLG b),vt)

(* Sorry about this---hopefully it's only a temporary inconvenience... *)

(* Conor notes...
Three things:

(1) We need the ability to suppress Undo marking, so that tactics composed
     from other tactics only leave one mark. Hence the wrapper tactical
     no_history, crudely implemented here in a reentrant fashion.
(2) Tacticals which work by backtracking need to make their own (non-user)
     Undo marks. They should do this with tacticalPushHist. Any such mark
     should be removed without fail, either with undo (if backtracking is
     necessary) or with discard (if it isn't)---discard throws away the
     mark without affecting the proof. This should ensure that the only
     marks which survive between user commands are user Undo marks.
(3) There is now a facility for attaching other structures to the history
     mechanism on an ad hoc basis---this is principally to support the
     Then tactical. Any such additional structure requires methods for
     "Init" (run at start of proof), "Mark" (run by pushHist), "Undo"
     (one step) and "Discard" (one step).
*)

local

	val HIST_HACK = ref 0;

(* 	fun doIt     f = f () 
	fun initKnot f = f="Init"
	fun markKnot f = f="Mark"
	fun undoKnot f = f="Undo"
	fun discKnot f = f="Discard"
 *)

	val initKnot = UndoKnots.KT.isIt "Init"
	val markKnot = UndoKnots.KT.isIt "Mark"
	val undoKnot = UndoKnots.KT.isIt "Undo"
	val discKnot = UndoKnots.KT.isIt "Discard"

	fun PushHist() = (* push Universes as a separate operation *)
	((HIST:= State(!COM,!QUEST,!NUN,!NSP,!Universes.UVARS,!HIST));
	 (* run Mark methods *)    
   	 (* List.map doIt (UndoKnots.seek_all_knots markKnot));( *)
	 (UndoKnots.do_all_knots markKnot))

        fun restoreAll (c,q,n,v,u,h) = (* pop Universes *)
    	(COM:=c;QUEST:=q;NUN:=n;NSP:=v;Universes.UVARS:=u;HIST:=h;())

   	fun restoreH (c,q,n,v,u,h) = (* pop Universes? *)
    	(HIST:=h;())

in

  fun markEnabled () = (!HIST_HACK) >= 0

  fun no_history tac () =
	    ((HIST_HACK := ((!HIST_HACK)-1));
	    (tac ());
	    (HIST_HACK := ((!HIST_HACK)+1)))
	    handle x => ((HIST_HACK := (succ (!HIST_HACK))); raise x)

  fun init_history() = 
	    ((* (message "initHist");*)
	     (HIST := NoProof);
	     (* List.map doIt (UndoKnots.seek_all_knots initKnot));( *)
	     (UndoKnots.do_all_knots initKnot))

  fun tacticalPushHist() = (* must be undone or discarded *)
	    ((* (message "tacticalPushHist");*)
	     PushHist())

  fun pushHist() = if (markEnabled ())
		       	    then ((* (message "pushHist"); *)
                            	  PushHist())
			 else ()

  exception UndoExn

  fun undo() =
      (case !HIST
	of State st => restoreAll st
	 | Proven(_,State st) => restoreAll st
	 | Initial => (NSP:= (!GOAL_CTXT); raise UndoExn)
	 | _ => bug"undo"
	 ;
       (* List.map doIt (UndoKnots.seek_all_knots undoKnot)); 
       (*(message "undo");*)( *)
       (UndoKnots.do_all_knots undoKnot)
       )

  fun discard() = (* Throws away history mark, but not proof *)
     (case !HIST
	of State st => restoreH st
	 | Proven(nvt,State st) => ((restoreH st);(proven nvt))
	 | Initial => (NSP:= (!GOAL_CTXT); raise UndoExn)
	 | _ => bug"discard"
      ;
      (* List.map doIt (UndoKnots.seek_all_knots discKnot)); 
      (*(message "discard");*)( *)
      (UndoKnots.do_all_knots discKnot))

end;

(********************************************************************)
(* tactic_wrapper ensures that the tactic it wraps obeys:           *)
(* (1) successful tactics mark history if enabled, then change      *)
(*       the state                                                  *)
(* (2) failing tactics neither mark history nor change state        *)
(********************************************************************)

  fun tactic_wrapper tac () =
    ( (tacticalPushHist());
      (no_history tac ());
      (if (markEnabled()) then () else discard ()) )
    handle x => ((undo());(raise x))


(* ******************************************************************* *)


(* ******************************************************************* *)
(* *** Goal, Save, Claim, Undo, KillRef, Next: for use by Toplevel *** *)

  fun Goal v = (let 
      	       	    val nun  = 0
		    val goal = (nun, v)
		    val com  = Var goal
		in 
      	           GOAL_CTXT := !NSP;
	      	   NUN := nun;
	      	   QUEST := [Unknown[goal]];
	      	   COM := com;
	      	   HIST := Initial
		end)
    
  fun Undo n = repeat n undo () handle UndoExn => ()

  fun UndoAll () = (let fun undoAll () = (undo () handle UndoExn => raise UntilExn)
    	       	    in  Until undoAll ()
		    end)

local
	fun killAll() = (UndoAll(); init_history()) (* bug detected at goals? *)
	fun killMsg tag = "Warning: forgetting a"^tag^"finished proof"
	fun killWrapper tag = (message(killMsg tag); killAll())
in

  fun KillRef() = if activeProofState() then killWrapper "n un"
    		  else if provenState() then killWrapper " "
    		       else()

end;

(* ****************************************************************** *)
(* goal management *)

  fun goals() = if activeProofState()
		  then case (!QUEST)
			 of Unknown(l)::q => (l,q)
			  |           _   => bug"goals"
		else failwith"no current goals"


(* 2011: new *)

      fun solve tacflg (s,n,new,close,V) =
      let
	 val (l,q) = goals()
      in 
	 

         (if tacflg
	 	then ()
	  else (Pretty.print_refine n V; pushHist(); ());
		    
	       putNamespace (subPrfCxt s);
	       putProofTerm (sub s (getProofTerm()));
	       putCurrentQuest (Unknown(erase_replace s n new l)::(eraseq s q));
					
	  close(); () (* return the new goals? *)
	  )
      end
  
      fun solved (res as (_,_,gs,_,_)) = if noMoreGoals gs 
      	  	   	   		    then (solve true res; true)
      	  	   	   		 else false (* raise Solve *)
   

(* *** each of these use magic number ~9999 and failGoal ****************** *)

local
  val abs_goal_name = Int.toString
  fun rel_goal_name (reverse,n) = (if reverse then "-" else "+")^(abs_goal_name n)
  fun failGoal msg goal_name = failwith (msg^" goal ?"^goal_name^" not found")
in

  fun goalIndex (g as (n,_)) = n
  fun goalType   (g as (_,c)) = c

  fun current_goals () = (#1 (goals()))

  fun current_goal_indexes () = List.map goalIndex (current_goals())

  fun subgoals() = case goals()
		     of ((nc as (n,c))::l,q) => (nc,l,q)
		      | (             [] ,_) => bug"subgoals"

  fun current_goal () = (#1 (subgoals()))

  fun current_goal_index () = goalIndex (current_goal())

  fun current_goal_type () = goalType (current_goal())

  fun goaln n = if n=(~9999) then (current_goal())
              else (n,assoc n (current_goals())
                      handle _ => failGoal "goaln:" (abs_goal_name n))

  fun goal_rel (relint as (reverse,n)) =
    let val (h,t,_) = subgoals() 
        val l = (h::t) (* (l, _) = goals() *)
    in nth (if reverse then List.rev l else l) (n+1) (* Utils.nth (n+1) = List.nth n *)
	handle Nth _ => failGoal "relative" (rel_goal_name relint)
    end

  (* does validation of the index relint, then returns its "real" index value *)
  fun rel_goal_index relint = goalIndex (goal_rel relint)
	    
  fun abs_goal_index n = n
      		      (* *** goalIndex (ASSOC n (#1 (goals())))		  *** *
		       * *** 	handle _ => failGoal "absolute" (abs_goal_name n) *** *)
	    
  fun goal9999() = current_goal()

(* ********************************************************************** *) 

  fun Claim v sbst (manager as (mkVar, eraseNew, close)) = (* mkVar eraseNew close = *)
    let
      val (l,q) = goals()
    in
      mkVar v; close();
      pushHist();
      QUEST := Unknown(l@(eraseNew sbst))::q
    end

(* *** 
(* *** based on manageVars: can/should we tighten this coupling? *** *)

  fun NEWClaim nam v sbst (manager as (mkVar, eraseNew, close)) = * NOT IMPLEMENTED *

 * ***)

(* ****************************************************************** *)
(* Subgoal mangement *)

  (* on veut d'abord chercher une preuve du sous-but n *)
  fun NextTac9999 () = ()

  fun Next n =
    let fun reorder n ((u as (p,_))::l) = 
      	    	    if p=n then (u,l) 
      		    else let val (v,l') = reorder n l in (v,u::l') end
	  | reorder n [] = failGoal"reorder: sub" (abs_goal_name n)
    in
      if n=(~9999) then NextTac9999() (* *** conor's magic number? *** *)
      else (QUEST:= let val (l,q) = goals() 
			val (u,l') = reorder n l
		    in  Unknown(u::l')::q
		    end;
	    ())
    end;

end;

(* ****************************************************************** *)
(* Save the proof of the current goal *)

fun Save name (frz_lg as (frz_flg,locGlob)) =
  case !HIST
    of Proven(((n,lg),vt),_) =>
      let                             (*  Save line vs Goal line! *)
	val name =
	  case (n,name)
	    of ("","") => failwith("cannot Save: no name provided")
	     | (x,"") => x
	     | ("",x) => x
	     | (x,y) => if x=y then x
			else failwith("cannot Save: two names provided: \""^
				      n^"\" and \""^name^"\"")
	val locGlob = (case (lg,locGlob)       (* as Local as possible *)
			 of (Global,Global) => Global
			  | _ => Local)
	val deps = ([]:string list) (* *** wot? no deps? *** *)

      in 		   (* ***  wot? no deps? *** *here*  *** *)
	(addBndGbl Bnd (Prefix(Let,Def,frz_flg,locGlob,[])) name vt; 
		    (* previously extendCxtGbl, deps = [] *)

	 init_history ();
	 message (Utils.StringUtil.dquote(name)^"  saved as "
		  ^(prLocGlob locGlob)
		  (* if locGlob=Local then "local, " else "global, " *)
		  ^", "
		  (* if (isFrozen frz_flg) then "frozen" else "unfrozen" *)
		  ^(prFrz frz_flg)
		  ))
      end
     | NoProof => failwith"no proof to save"
     |    _    => failwith("cannot Save \""^name^"\": proof unfinished")


(* ****************************************************************** *)
(* Equiv, normalisation and expansion of the current goal *)

   fun Equiv (sbst:substitution) (V:cnstr) =
    let
	val (mkVar,eraseNew,close) = manageVars()
	val ((nc as (n,c)),l,q) = subgoals()
    in
      case ParTm.par_unif sbst V c of
	SOME(s) =>
	  let val newT = sub s V
	      val new = (n,newT)::(eraseNew s)
	  in (pushHist();
	      QUEST:= Unknown(erase_replace s n new (nc::l))::(eraseq s q);
          (*  COM:= sub [(n,LabVT(StrongCast,Var(n,newT),c))] (!COM);  *)
	      close())
	  end
      | NONE => failwith"not convertible"
    end

local

        val norm = UMopen.UMnorm 

	fun NFSQUASH (nf : cnstr -> cnstr) _ = 
	    let
		val ((n,c),l,q) = subgoals()
	    in 
	       (pushHist();
		QUEST:= (Unknown((n,nf c)::l))::q)
	    end
in

   fun Normal () = NFSQUASH norm ()
   fun Hnf    () = NFSQUASH whnf ()
   fun Dnf    n  = NFSQUASH dnf n

   fun Expand path nams = NFSQUASH (dnf o (Expand.Expand path nams)) ()
   fun ExpAll path  m	= NFSQUASH (dnf o (Expand.ExpandAll path m)) ()

end; 

(* ****************************************************************** *)
(* intros, in all its majesty: could optimise a little *)

  local

    fun Addq l = (* shuffle subgoals at the same level when doing intros *)
      if List.null l then (fn(q:quest) => q) (* I *)
      else fn Unknown(l1)::q => Unknown(l@l1)::q     (* add new subgoals *)
    	    |              q => Unknown(l)::q;

    fun mk_goal c = ((NUN:= succ(!NUN);!NUN),c) (* manageVars().mkVar? *)

    fun push_so_far ((n,c),l,q) h c' =
      if Utils.UNSAFEeq (c,c') then () (* ********** pointer equality !!! *********** *)
      else let val gl = mk_goal c'
	   in (* get a new level of subgoals while pushing the old ones *)
	     (QUEST:= Unknown([gl])::((Push(n,h,!COM))::(Addq l q));
	      COM:= Var(gl); () )
	   end

    fun mk_name nam s = mkNameGbl(if (isNullString nam) 
    		      		   then if (isNullString s) 
				   	 then HYPNAME (* "H" *)
				     	else s
				  else nam)
  in

    fun do_intros (flgs as (hnfFlg,autoFlg)) count lst =
      let
	fun intros_rec count lst c push =
	  let (* *** how do we make this safe? *** *)
	    fun sig_intro (sigBod as (_,s,tl,tr)) =
	      let
		val ((n,c),l,q) = subgoals()
		val goal_l = mk_goal tl
		val tr = subst1 (Var goal_l) tr
		val goal_r = mk_goal tr
		(* **********  Tuple is unsafe ******* *)
		val sbst = mkSubst1(n,Tuple(Bind sigBod,[Var goal_l,Var goal_r]))
	      in (* no need for Addq here *)
		(QUEST:= eraseq sbst (Unknown(goal_l::goal_r::l)::q);
		 COM:= sub sbst (!COM); () )
	      end
	    fun pi_intro nam nams ((_,vis),s,c1,c2) push =
	      let
	      (* make the name for the new binding *)
		val nam = mk_name nam s
	      (* better: create and push new assumption *)
		val newBnd = mkLdaGbl vis nam (Machine.ConsiderTerm c1)
		val _ = addNamespace (newBnd)
	      in (* repeat on the instantiated body: could optimise this *)
		intros_rec (succ count) nams (subst1 (Ref newBnd) c2) push (* *** *)
	      end
	    fun let_intro nam nams ((_,vis),s,c1,c2) push =
	      let (* identical to Pi case, but for Let/Lda *)
		val nam = mk_name nam s
		val newBnd = mkLetGbl vis nam (Machine.ConsiderTerm c1)
		val _ = addNamespace (newBnd)
	      in  
		intros_rec (succ count) nams (subst1 (Ref newBnd) c2) push (* *** *)
	      end
	  in
	    case if autoFlg then [""] else lst
	      of "#"::nams => (case whnf c
				 of Bind(b as ((Sig,_),_,_,_)) =>
				   (push c; sig_intro b;
				    do_intros flgs count nams)
				  | _ => failwith"cannot do Sigma intro")
	       | nam::nams =>
		   (case if hnfFlg then whnf c else c
		      of Bind(b as ((Pi,_),_,_,_)) => pi_intro nam nams b push
		       | Bind(b as ((Sig,_),_,_,_)) =>
			   if autoFlg then (push c; sig_intro b;
					    do_intros flgs count nams)
			   else failwith("SIG Intro with improper token: "^nam)
		       | Bind (b as ((Let,_),_,l,r)) => let_intro nam nams b push
		       | _  => if autoFlg then (push c; count)
			       else failwith"goal has wrong form for intros")
	       | [] => (push c; count)
	  end
	val (sgs as ((_,c),_,_)) = subgoals() 
	val h = latestTsGbl()
      in
	intros_rec count lst c (push_so_far sgs h)
      end
  end;

(* ****************************************************************** *)
(* *** global operations and additions: REORGANISE!!! *** *)

(* freezing and unfreezing: see context.sml *)
fun Freeze ns = FreezeCxt ns (getNamespace())

fun Unfreeze ns = UnfreezeCxt ns (getNamespace())		
		
fun addLabel tn = addNamespace (mkLabelBnd tn)

(* reductions in Contexts *)

fun addReduct VT = addNamespace (mkReductBnd VT) (* synonym for SaveReductGbl *)

fun SaveReductGbl VT = addNamespace (mkReductBnd VT)
(*  let fun saveReduct (v,t) cxt =
    (Bd{ts=timestamp(),frz=ref UnFroz,param=Global,deps=[],kind=Red,
	bd=((Sig,VBot),"",v,t)})::cxt
  in NSP:= saveReduct VT (getNamespace())
  end; *)

(* DEEP dependency of a subject ref on an object ref: for discharge/strengthening *)
val Dep_debug = ref false;

fun DEPENDS skip br_obj br_sbj =
  let
    val nam = ref_nam br_obj

    fun flre str br = 
      if (!Dep_debug)
	 then message(str^nam^" "^ref_nam br^" "^
			concat_space (List.map ref_nam skip))
      else ();
	 

    fun Depends c =  (* DEEP dependency of a term on a name *)
    case c
      of (Ref br) => ( flre "**Dep " br ; DEPENDS skip br_obj br ) 
	(* if (!Dep_debug)
	   then message("**Dep "^nam^" "^ref_nam br^" "^
			concat_space (List.map ref_nam skip))
	 else ();
	 DEPENDS skip br_obj br *)
       | (App((c,cs),_)) => (Depends c) orelse (List.exists Depends cs)
       | (Bind(_,_,c,d)) => (Depends d) orelse (Depends c)
       | (Tuple(T,l))    => (Depends T) orelse (List.exists Depends l) 
       | (CnLst l)       => List.exists Depends l
       | (Proj(_,c))     => Depends c
       | (RedTyp(_,c))   => Depends c
       | (Var(_,c))      => Depends c
       | _               => false
  in
    (not (List.exists (sameRef br_sbj) skip)) andalso
    ref_ts br_obj <= ref_ts br_sbj andalso
    ((* if (!Dep_debug)
       then message("**DEP "^nam^" "^ref_nam br_sbj^" "^
		    concat_space (List.map ref_nam skip))
     else (); *)
     flre "**DEP " br_sbj ; 
     sameRef br_sbj br_obj orelse
     let val (v,t) = ref_vt br_sbj
     in  Depends v orelse Depends t
     end orelse
       List.exists (DEPENDS (br_sbj::skip) br_obj)
           (List.map searchNamespace (ref_deps br_sbj)))    (** ??? **)
  end;

(* ********************************************************************* *)
(* should work fine with new ? binder---the clever bit is now in Machine *)
(* except that we need to get the prVis after the oper is run            *)

(* vital! should it be called after every destructive update of NSP? *)
fun MakeAllPats() = (* *** where to put this? anywhere BEFORE discharge/forget *** *)
  let 
      fun addRed br = if ref_isRed br
      	  	      	 then UMopen.add_reductions (ref_red br)
      	  	      else () 
  in (UMopen.init_reductions(); 
      List.app addRed (List.rev (unCxt (getNamespace()))))
  end;

val disch_debug = ref false 

local
	val composeSubRef1 = Subst.composeSubRef1 o Subst.mkAssign

  fun spotVis (Bind ((_,v),_,_,_)) = prVis v
    | spotVis _ = ShowForce

  fun disch_debug_report msg (vt as (v,t)) = 
     if !disch_debug
     	then (prs msg;Pretty.prnt_vt vt)
	else ()

  fun dk (br,(left,deltas,moved)) = (* 2011: List.foldl *)
    let
      val _ = (prs(" "^ref_nam br))

      fun discharge oper deps (vt as (v,t)) br_sbj =
	let
	  val _ = disch_debug_report "\n** disch debug **  " vt
	      	  (* if !disch_debug
		    then (prs("\n** disch debug **  ");
			  prnt_vt vt)
		  else ()*)
	  (* we must remove a ref from deps once it is discharged *)
	  fun operate (br, vcvd as (vt as (v,t),cs,vs,deps)) = (* 2011: List.foldl *)
	    ((*if !disch_debug
	       then (prs("\n**operate** "^ref_nam br^", "); prnt_vt vt)
	     else ()*)
	     disch_debug_report ("\n**operate** "^ref_nam br^", ") vt;
	       if (depends br v orelse depends br t orelse
		   (List.exists (DEPENDS [br_sbj] br)
		    (List.map searchNamespace deps)))
		 then case ref_bind br
			of Lda => let val vt as (v,t) = oper vt br
                                  in (* need to get vis after oper *)
                                  (vt,
				   (Ref br)::cs,
				   (spotVis v)::vs,
				   filter_neg (sameNam br) deps)
                                  end
			 | Let => (Machine.letize vt br,cs,vs,
				   filter_neg (sameNam br) deps)
			 | _ => bug"funny Discharge"
	       else vcvd)
	in 
	  List.foldl operate (vt,[],[],deps) moved (* 2011: List.foldl *)
	end

      fun globalDefn ts deps vt br_sbj =
	let
	  val (vt,cs,vs,ndeps) =
	    discharge Machine.abstract deps (subRef_pr deltas vt) br_sbj
	  val br' = ref_updat_vtdeps br vt ndeps
	in  
	  (br'::left,
(*	   compose subRef [(ts,MkApp((Ref br',cs),vs))] deltas, *)
	   composeSubRef1 (ts,MkApp((Ref br',cs),vs)) deltas, 
	   moved)
	end

      fun globalDecl ts deps vt br_sbj =
	let	           (* a global decl depends on everything! *)
	  val (vt,cs,vs,ndeps) =
	    discharge Machine.generalize deps (subRef_pr deltas vt) br_sbj
	  val br' = ref_updat_vtdeps br vt ndeps
	in  
	  (br'::left,
(*	   compose subRef [(ts,MkApp((Ref br',cs),vs))] deltas, *)
	   composeSubRef1 (ts,MkApp((Ref br',cs),vs)) deltas, 
	   moved)
	end

      fun reductions ts deps vt br_sbj =
	let
	  val (vt,cs,vs,ndeps) =
	    discharge Machine.abstract deps (subRef_pr deltas vt) br_sbj
	  val br' = ref_updat_vtdeps br vt ndeps
	in  
	  (br'::left,deltas,moved)
	end

      fun localDecl ts n vt =
	let
	  val vt = subRef_pr deltas vt
	  val br'= ref_updat_vt br vt
	in
	  (left,
(* 	   compose subRef [(ts,Ref br')] deltas, *)
	   composeSubRef1 (ts,Ref br') deltas,
	   br'::moved)
	end

      fun localDefn ts n vt =
	let
	  val vt = subRef_pr deltas vt
	  val br'= ref_updat_vt br vt
	in
	  (left,
(* 	   compose subRef [(ts,Ref br')] deltas, *)
	   composeSubRef1 (ts,Ref br') deltas,
	   br'::moved)
	end

      fun dk_ br Bnd ts Global deps ((Let,_),_,v,t) = globalDefn ts deps (v,t) br 
        | dk_ br Bnd ts Global deps (_,_,v,t) = globalDecl ts deps (v,t) br 
        | dk_ br Bnd ts Local deps ((Let,_),n,v,t) = localDefn ts n (v,t)  
        | dk_ br Bnd ts Local deps (_,n,v,t) = localDecl ts n (v,t)  
        | dk_ br (GenTag _) ts Global deps ((Let,_),_,v,t) = globalDefn ts deps (v,t) br 
        | dk_ br (GenTag _) ts Global deps (_,_,v,t) = globalDecl ts deps (v,t) br 
        | dk_ br (GenTag _) ts Local deps ((Let,_),n,v,t) = localDefn ts n (v,t)  
        | dk_ br (GenTag _) ts Local deps (_,n,v,t) = localDecl ts n (v,t)  
        | dk_ br Red ts _ deps (_,_,v,t) = reductions ts deps (v,t) br 
        | dk_ br (Mrk _) _ _ _ _ = (br::left, deltas, moved)
        | dk_ br (Config _) _ _ _ _ = (br::left, deltas, moved)
        | dk_ br (LabelTag _) _ _ _ _ = (br::left, deltas, moved)
	| dk_ _ _ _ _ _ _ = bug"dk"

    in dk_ br (ref_kind br) (ref_ts br) (ref_param br) (ref_deps br) (ref_bd br) 
(*
      case ref_body br of
	{kind=Bnd,ts,param=Global,deps=deps,bd=((Let,_),_,v,t),...} => 
	  globalDefn ts deps (v,t) br
      | {kind=Bnd,ts,param=Global,deps=deps,bd=(_,_,v,t),...} =>
	  globalDecl ts deps (v,t) br
      | {kind=Bnd,ts,param=Local,bd=((Let,_),n,v,t),...} =>
	  localDefn ts n (v,t)
      | {kind=Bnd,ts,param=Local,bd=(_,n,v,t),...} =>
	  localDecl ts n (v,t)
      | {kind=GenTag _,ts,param=Global,deps=deps,bd=((Let,_),_,v,t),...} => 
	  globalDefn ts deps (v,t) br
      | {kind=GenTag _,ts,param=Global,deps=deps,bd=(_,_,v,t),...} =>
	  globalDecl ts deps (v,t) br
      | {kind=GenTag _,ts,param=Local,bd=((Let,_),n,v,t),...} =>
	  localDefn ts n (v,t)
      | {kind=GenTag _,ts,param=Local,bd=(_,n,v,t),...} =>
	  localDecl ts n (v,t)
      | {kind=Red,ts,deps=deps,bd=(_,_,v,t),...} =>
	  reductions ts deps (v,t) br
      | {kind=Mrk(_),...} => (br::left, deltas, moved)
      | {kind=Config(_),...} => (br::left, deltas, moved)
      | {kind=LabelTag _,...} => (br::left, deltas, moved)
      | _ => bug"dk"
 *)
    end

in

  fun dischg nam msg =
    if activeProofState() then failwith"No Discharge in proof state"
    else let
	   val  t = start_timer()
	   val (hit,new,old) = (* Context.splitCxt *)
                splitCxt (mtnNam nam) (nam^" undefined") (getNamespace())
	   val _ = prs("Discharge and "^msg^"... ")
	   val _ = init_history()
	   val res = List.foldl dk (unCxt old,nilS,[]) (hit :: (unCxt new)) 
	   val _ = prnl()
	   val _ = message (print_timer t) (* message("   (* "^(makestring_timer t)^" *)") *)
         in res
	 end
end;

local
  fun dischState brs = (NSP:= mkCxt brs; MakeAllPats(); prnl())
in
  fun DischargeKeep nam = let val (left,_,moved) = dischg nam "keep"
			  in  dischState (moved@left)
			  end
  and Discharge nam = let val (left,_,_) = dischg nam "forget"
		      in  dischState left
		      end
end;

local
  fun forget f nopMsg killMsg smsg =
    let
      val _ = splitCxt f nopMsg (getNamespace())  (* to see if nam is there *)
      val _ = KillRef()                            (* Forget forces Kill *)
      fun sr_ (br::brs) = (* changed 2011 *)
      	  if ref_isInfix br
	     then 
	     	  let val (b,c,d) = ref_infix br
		  in (Infix.infix_forget b; sr_ brs)
		  end 
	  else (if f br then brs else sr_ brs)
	| sr_ []        = failwith killMsg 
      val sr = (mkCxt o sr_ o unCxt) (* changed 2011 *)
    in  (NSP:= sr (getNamespace()); MakeAllPats(); smsg())
    end

  fun ForgotMark mrk = "forgot back through Mark "^Utils.StringUtil.dquote mrk

in

  fun Forget nam =
      let
	  val qnam = Utils.StringUtil.dquote nam

	  (*** The interface (Proof General) would like to know when
	  we retract across module boundaries. We therefore keep track 
	  of module boundary in the context. ***)
	  val module = ref NONE
      in
	  forget (fn br => if (ref_isMrk br)
			       then (module := SOME (ref_mrk br); false)
			   else sameNam br nam)
	  ("Forget is no-op; "^qnam^" not in namespace")
	  ("Forget forced KillRef; "^qnam^" no longer in namespace")
	  (fn () =>
	   ((case !module of
	       NONE => ()
	     | SOME mrk => loudmessage (ForgotMark mrk));
		message ("forgot back through "^nam)))
      end

  fun ForgetMrk mrk =
    forget (sameMrk mrk)
           ("ForgetMark is no-op; \""^mrk^"\" not in namespace")
	   ("bug at ForgetMark")
	   (fn () => loudmessage (ForgotMark mrk))
end;

fun addLabel tn = addNamespace (mkLabelBnd tn)

local
  fun gotB b = if ref_isBnd b then SOME (Ref b,ref_typ b) else NONE
in 
  fun spotLabel tag =
      let 
          fun s2_ [] = NONE
            | s2_ (b::t) = let val k = ref_kind b
                           in  case k
                                 of LabelTag (tag',id) =>
				    if tag=tag'
                                    then gotB (searchNamespace id)
                                         handle _ => NONE
                                    else s2_ t
                                  | GenTag tag' => if tag=tag'
                                                  then gotB b
                                                  else s2_ t
                                  | _ => s2_ t
                           end
          val s2 = s2_ o unCxt
      in  s2 (getNamespace())
      end
end; 

fun addConfig config = addNamespace (mkConfigBnd config)

fun addConfigInfix_ (name,assoc,prec) = (* depends on global structure Infix *)
    if Infix.infix_register name assoc prec 
       then
            (addConfig("Infix", (name, Infix.strAssoc assoc, Infix.strPri prec)))
    else ()

fun addConfigInfixNAssoc name = addConfigInfix_ (name,Infix.NAssoc,0)

fun addConfigInfix (name,b,prec) = addConfigInfix_ (name,Infix.mkAssoc b,prec)

fun addConfigObjects () = addConfig ("Objects",("","","")) 
fun addConfigNoObjects () = addConfig ("NoObjects",("","","")) 

(* 
   fun findConfigCxt key fail =
      let
         fun fc2 [] = fail
           | fc2 ((Bd{kind=Config(a,cfgdata),...})::tail) = (* 2011 *)
                if (a=key) then cfgdata else fc2 tail
           | fc2 (_::tail) = fc2 tail
      in
         fc2 
      end
*) 
    
   fun findConfig key fail = findConfigCxt key fail (getNamespace()) 

(* 
        let
            fun fc2 [] = fail
              | fc2 ((Bd{kind=Config(a,cfgdata),...})::tail) =
                if (a=key) then cfgdata else fc2 tail
              | fc2 (_::tail) = fc2 tail
        in
            fc2 (getNamespace())
        end
*) 

fun addMark (m,i,t) = addNamespace (mkMarkBnd (m,i,t))

(************ theory packaging **************)

(* Mark the start of theory "nam" *)
fun StartTheory nam =
  let
    (*fun addThry() = NSP := (Bd{kind=StThry nam,
			       ts=timestamp(),
			       frz=ref UnFroz,
			       param=Global,
			       deps=[],
			       bd=((Sig,VBot),"",Bot,Bot)})::(!NSP)*)
    val _ = if activeProofState()
	      then failwith"Cannot start a theory in proof state"
	    else ()
    val _ = if isNewName nam
	      then ()
	    else failwith("Name \""^nam^"\" already in namespace")
    val _ = message("Starting theory \""^nam^"\"")
  in
    NSP := addThryCxt nam (getNamespace()) (* addThry() *)
  (* addNamespace (mkThryBnd nam) *)  
  end;

local
   fun sub_Ref s = 
      let fun sub_rec n =
	  fn (Ref br)  => (Mod(assoc (ref_ts br) s n) handle Assoc => UMod)
	   | (Var b)   => mkVar (sub_rec n) b
	   | (App b)   => mkApp (sub_rec n) b
	   | (Bind b)  => mkBind sub_rec n b
	   | (Tuple b) => mkTuple (sub_rec n) b
	   | (CnLst b) => mkCnLst (sub_rec n) b
	   | (Proj b)  => mkProj (sub_rec n) b
	   | (RedTyp b)=> mkRedTyp (sub_rec n) b
	   | (LabVT b) => mkLabVT (sub_rec n) b
	   | _         => UMod
       in sub_rec 1
       end

   fun subRef s = share (sub_Ref s)

in

fun EndTheory nam =
  let

    val _ = if activeProofState()
	      then failwith"No \"EndTheory\" in proof state"
	    else ()

    val (_,newcxt,oldcxt) =
      splitCxt (fn br => ref_stThry br = SOME nam) (nam^" undefined") (getNamespace())

    val _ = prs("Package theory named \""^nam^"\": ")

    val newbrs = unCxt newcxt

    fun pack (br::brs) sbst lvts =
      let
	val rnbr = ref_nam br
      in
	if not (ref_isDefn br)   (****  allow decls and frozen  *****)
	  then (message"";
		failwith("Attempt to pack a non-definition, \""^
			 rnbr^"\", in theory "^nam^"\"."))
	else let
	       val _ = prs(" "^rnbr)
	       val osubRef = subRef sbst 
	       val lvt = MkLabVT(Name rnbr,
				 (* improve sharing by using VT pair *)
				 osubRef (ref_VAL br),
				 osubRef (ref_TYP br))
	       (* don't have to compose sbsts in this special case *)
	       val nsbst = (ref_ts br,fn m => Proj(Labl rnbr,Rel m))::sbst
	     in
	       pack brs nsbst (lvt::lvts)
	     end
      end
	 | pack [] _ lvts = lvts

    val lvts =  List.rev (pack newbrs [] [])

    val _ = prnl()

    val thry = MkThry lvts 

  in 
     (* *** !!! *** *)
     NSP:= addThyGbl nam thry oldcxt (* *** addBndCxt newBnd oldcxt *** *) 

  end

end; 

end; (* of local *nf defns *)

end; (* FunNamespace *)

