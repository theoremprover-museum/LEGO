(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* top level *)

functor FunToplevel(
	structure Term : TERM
   	structure Subst : SUBST 
   	structure UMopen : UMOPEN
   	structure ParTm : PARTM
   	structure Namespace:NAMESPACE
	structure Engine : CONSTRUCTIVEENGINE
     	structure Synt:SYNT
	structure Pretty : PRETTY 
     	structure Error:ERROR 
     	sharing 
      		type Term.cnstr 
		   = Subst.cnstr 
		   = UMopen.cnstr 
		   = ParTm.cnstr 
		   = Namespace.cnstr 
		   = Engine.cnstr 
		   = Pretty.cnstr 
		   = Error.cnstr 
 	and
     	     	type Engine.cnstr_c 
		   = Synt.cnstr_c 
     	and 
		type Term.binding
		   = Subst.binding
		   = Namespace.binding
		   = Pretty.binding
     	and 
		type Namespace.context
		   = Engine.context
		   = Pretty.context
     	and 
		type Subst.substitution
		   = ParTm.substitution
		   = Namespace.substitution
		   = Engine.substitution
     	and 
		type Term.Frz
		   = Namespace.Frz
     	and 
		type Term.LocGlob
		   = Namespace.LocGlob
	) 
(* *** * 
structure Toplevel 
 * *** *)
	: TOPLEVEL 
 =

struct

val pr_debug = ref false;

	type cnstr_c = Engine.cnstr_c

local 

        val failwith = Utils.Except.failwith
	val bug = Utils.Except.bug

	open Utils.Timing 
	open Printing 

	val Bot = Term.Bot 
	val mkLG = Term.mkLG 
	val mkFrz = Term.mkFrz 

	val global = true

	val unfroz = true
	val froz   = false

	val isAnnotating = Annotate.isAnnotating 
	val pbpAnnotate = Annotate.pbpAnnotate 
	val interactive = Annotate.interactive

(*!*)	val prnt_goals = Pretty.prnt_goals o List.map (Namespace.unGoal) o Namespace.unGoals
	

in 

  (* new: 2009.12.09 "doesn't solve goal" :JHM *)
  (*  exception Solve = Synt.Solve *)
  (* but *never raised* here: except in andE in Tactics! *)
  (* 2011: move andE etc. to Logic; add RefineHandle_c for this case *)

  local 
        val pnf = UMopen.UMpnf

        val par_tm = ParTm.par_tm

	(* toplevel goal: save for use at end of proof *)
	val TLGOAL = ref Bot;
	val TLNAME = ref (Utils.StringUtil.nullString,global);
	val TLTIMER = ref (start_timer())
	fun checkTLTIMER () = #usr(check_timer(!TLTIMER))

	fun GOAL_ V namLocGlob = (Namespace.Goal V;
		       	       	  TLGOAL:= V;
		       		  TLNAME:= namLocGlob;
		       		  TLTIMER:= start_timer())

	fun qed () = message("*** QED ***"^print_timer (!TLTIMER))
  in
	fun GOAL V namLocGlob = let 
	    	     	      	    val V = pnf V    (* *** UMpnf ??? *** *)
		     		in  
				    GOAL_ V namLocGlob
		     		end

	fun QED () = (* here it comes! *)
	let
	(* you get the completed cnstr *)
	  val TLPRF = pnf (Namespace.getProofTerm()) (* *** UMpnf ??? *** *)

	(* you get a concrete term out of it: this does the occur check! *)
	  val cpt = if Term.pure TLPRF then Engine.unEval TLPRF else bug"Pr:impure proof"
	  val refine_time = checkTLTIMER () (* #usr(check_timer(!TLTIMER)) *)

	(* you run the Constructive Engine to get a type for it *)
	  val com = Engine.fEvalTyp cpt
	  val retype_time = checkTLTIMER () (* #usr(check_timer(!TLTIMER)) *)

	(* you test conversion with the proposed type *)
	  val rechck = par_tm com (!TLGOAL)
	  val rechck_time = checkTLTIMER () (* #usr(check_timer(!TLTIMER)) *)

	(* then you do some debugging of all the checking in parallel *)
	  val _ = if (!pr_debug) then
	    (prs("**pr_deb: refin "^mks_time refine_time^
		 " retyp "^mks_time(sub_time(retype_time,refine_time))^
		 " rechk "^mks_time(sub_time(rechck_time,retype_time)));
	     if earlier(refine_time,sub_time(rechck_time,refine_time))
	       then message"check and recheck times adrift!!!!"
	     else message"")
		  else()
	in
	  if rechck (* *** QED!!! *** *)
	    then (Namespace.QED (!TLNAME,(TLPRF,!TLGOAL)); qed ())
	  else bug"Pr" (* types didn't match *)
	end;

	(* for Conor in OLEG *)
	fun legoGoalName () = #1 (!TLNAME)

  end; (* local TL ref bindings *)

(* initialize toplevel *)
val init_toplevel = Namespace.init_history

(* Save flags and defaults: everything is unfrozen until it's frozen! *)
local 
      val Save_frz_default = ref unfroz
in 
   fun ConfigSaveFroz ()   = (Save_frz_default:=froz)
   fun ConfigSaveUnFroz () = (Save_frz_default:=unfroz)

   fun SaveDefault (id, locglb) = Namespace.Save id (mkFrz(!Save_frz_default),mkLG locglb)

   fun Save flg id = Namespace.Save id (mkFrz flg,mkLG global)

end;

(* Putting PR and DECH together is ugly; but it's the only way I (* who? *)
 * can get "auto discharge".  Notice DECH is now hidden from users *)

(* 2011: DECHWrapper encapsulates behaviour, but at huge run-time cost! *)

local 

      fun pr() = Pretty.prt_context_ref (* 2011: refactor prtContext *)
	       	 (Namespace.topContextBeforeProof())
		  (Namespace.getNamespace())

in 

fun Pr() = 
  let 
    fun DECH () = (*
    	     	  let 
    	     	      fun pr ()    = (Namespace.DECH(); Pr())
		      fun dech ()  = (Namespace.DECH(); DECH())
    	     	      fun prgs gs  = (PR())
    	     	  in 
		      Namespace.DECHWrapper pr dech prgs () 
		  end *)
(*  *)
      case (Namespace.getCurrentQuest()) of   (* discharge function *)
      	   		     []   => (Namespace.DECH(); Pr())
      | Namespace.Push(n,m,c)::_  => (Namespace.DECH(); DECH())
      | Namespace.Unknown(gs)::_  => if Namespace.noMoreGoals gs
      				     	then (Namespace.DECH(); DECH())
      				     else (PR())

  in
(* 

    Namespace.DECHWrapper QED DECH prnt_goals ()
 *)

    case (Namespace.getCurrentQuest()) of
      	 		   [] 	=> QED () (* *** QED!!! *** *)
    | Namespace.Push(n,m,c)::_  => DECH()
    | Namespace.Unknown(gs)::_  => if Namespace.noMoreGoals gs
      				      then (DECH())
      				   else (prnt_goals gs)
      				        (* *** now tests isInteractive () *** *)      			       	(* *** if interactive() then prnt_goals gs else () *** *)
  end

and PR() = if Namespace.activeProofState()
	      then ((if interactive() (* *** bug in control flow??? *** *)
		   	then 
			     (if isAnnotating()  (* *** annotation *** *)
			     	 then message(pbpAnnotate"Start of Goals") 
				else ();
				pr()) 
			 else ());	
			 Pr();
			     (if isAnnotating()  (* *** annotation *** *)
			     	 then message(pbpAnnotate"End of Goals") 
				else ()))
	   else if Namespace.provenState() 
		   then message"all goals proven!"
		else failwith"No refinement state"

and prAnnotating() = if isAnnotating() then PR() else Pr() (* *** annotation *** *)

end; 

local
	val failSORT = Term.failSORT
in

(* 2011: unify these two functions?  *
 * allow "Goal" in unfinished proofs *
 * to spawn a "Claim"... or "Lemma"? *)

fun Claim v_c =
  let
      val (manager as (mkVar,eraseNew,close)) = Namespace.manageVars()
      val ((V,T),sbst) = Engine.EvalRefine mkVar v_c (* 2011 *)
  in
      if Namespace.isSort T
      	 then (message"Claim "; Pretty.legoprint V;
	       Namespace.Claim V sbst manager; (* *** (*mkVar eraseNew close*) *** *)
	       prAnnotating())
	else failSORT"the subject of a Claim"
  end

fun Goal v_c (namLocGlob as (nam,_)) = 
  if Namespace.activeProofState()
    then (* *** debatable??? consider instead doing NEWClaim nam v_c? *** *)
    	 failwith"Cannot use 'Goal' during a proof" 
  else if nam<>"" andalso (not (Namespace.isNewName nam))
	 then failwith(Utils.StringUtil.dquote(nam)^" already in namespace")
  else (* now we actually do get a Goal off the ground *)
    let 
      val (V,T) = Engine.fEval v_c
    in  
      if Namespace.isSort T (* 2011: Namespace.KillRef first? *)
       	 then (message("Goal "^nam); 
	       (*prs nam; prnl();*)
	       GOAL V namLocGlob;
	       prAnnotating())
	else failSORT"the subject of a Goal"
    end;

end;

local
	fun undoFail () = failwith"Cannot undo: not in proof state"
	fun undoWrapper msg f a = if Namespace.proofState() (* prAnnotating() ??? *)
	    		      	     then (f a; message("Undo "^msg); PR()) 
				  else undoFail ()
in

   fun Undo n =  undoWrapper (Int.toString n) (Namespace.Undo) n

   val UndoAll = undoWrapper "All" (Namespace.UndoAll)

end

fun KillRef() = (Namespace.KillRef(); message "KillRef: ok, not in proof state");

(* to apply tactics *)
fun appTac f x = if Namespace.activeProofState()
    	       	    then (Namespace.tactic_wrapper (fn () => ((f x);())) ())
		 else failwith"no active goals"

fun      AppTac f x = (appTac f x; PR())
fun smallAppTac f x = (appTac f x; prAnnotating());

val Next = appTac (fn n => (Namespace.Next n; message("Next "^Int.toString n)));

val intros_debug = ref false;

fun IntrosTac hnfFlg n l = (Namespace.Next n; Namespace.do_intros (hnfFlg,null l) 0 l)

fun Intros hnfFlg n =
      smallAppTac
        (fn l => let
		   val names  = List.map (Utils.StringUtil.wildcard) l
		   val show_l = Utils.StringUtil.concat_space names
		   val _ = if (!intros_debug)
			     then (prs"**intros_debug**"; prsp(); pri n; prsp();
				   prs show_l; prsp(); prb hnfFlg; prnl())
			   else ()
		   val count = IntrosTac hnfFlg n l
		 in
		   prs(if hnfFlg then "Intros" else "intros"); prsp(); 
		   prs"("; pri count; prs")"; prsp(); message show_l;
		   if interactive() andalso not (isAnnotating())
		       then Pretty.prt_context_dpth count (Namespace.getNamespace())
		        (* refactored prt_intros 2011 *)
		   else ()
		 end);

(* *** 2011: autotac now not required by andE in Logic; *** *
 * BUT: idea was to apply the autotac ONLY to those 
 * NEW goals generated by e.g. Synt.resolve_c, Synt.solve     
 *)

(* new/refactoring, but mad *)
(* *** *)
  type autotac = Synt.autotac 

  fun mkAuto tac = tac

  fun unAuto tac = tac

  val nullTac = mkAuto (Synt.nullTac)

(* *** *)

  val AutoTac = ref nullTac

  fun getAutoTac() = !AutoTac
  fun setAutoTac tac = (AutoTac:= tac)

(* tidy up the AutoTac mess *)

local (* I moved this to Synt: now no-one should touch it *)
   (* fun solve = ... *)
   fun raiseSolve () = failwith"Solve: doesn't solve goal!"

in

   fun RefineWithTac_a n m v   tac  = (Synt.Solve_a true n m v (unAuto tac)  
       		       	     	       handle Synt.Solve => raiseSolve() )

   and RefineAutoTac_a n m v        = RefineWithTac_a n m v (getAutoTac())
   and RefineTac_a     n m v        = RefineWithTac_a n m v nullTac

   and RefineRaise_c n m v_c        = (Synt.Solve_c true n m v_c nullTac)

   and RefineHandle_c n m v_c tac_c = (RefineRaise_c n m v_c 
       		      	  	       handle Synt.Solve => tac_c v_c)

   and RefineWithTac_c n m v_c tac  = (Synt.Solve_c true n m v_c (unAuto tac) 
       		       	     	       handle Synt.Solve => raiseSolve() )

   and RefineAutoTac_c n m v_c      = RefineWithTac_c n m v_c (getAutoTac())
   and RefineTac_c     n m v_c      = RefineWithTac_c n m v_c nullTac

   and RefineWith      n m v_c tac  = ((Synt.Solve_c false n m v_c (unAuto tac) 
				        handle Synt.Solve => raiseSolve() ); 
       		       	       	       prAnnotating())

   and RefineAuto      n m v_c      = RefineWith n m v_c (getAutoTac()) 
(*   and Refine          n m v_c      = RefineWith n m v_c (getAutoTac()) (* nullTac? *)*)

   and Refine          n m v_c      = ((Synt.Solve_s false n m v_c 
				        handle Synt.Solve => raiseSolve() ); 
       		       	       	       prAnnotating())


(* 2011: no longer needed, as Immed directly defined below *  

   and SolveImmed n m v_c = Synt.SolveImmed_s n m v_c

 * ******************************************************* *)

end; (* local fun solve: now it's safely hidden away, encapsulated in Synt *)

(* ******** 2011: moved Immed and Assumption from Tactics; tweaked ********** *)
(* Only one UNDO per IMMED *)
exception Immed_tac;

fun immed_tac ex n = 
(* 2011 version *)
    let fun it_rec (br::brs) = 
	if (Namespace.inContextBeforeProof br) (* stop! *)
(***)	    then if ex then raise Immed_tac else false  (* unsuccessful exit *)
	else if Synt.SolveImmed_s n 0 (Engine.mkRef_c (Term.ref_nam br)) (* 2011 *)
(***)		 then true				(* successful exit *)
		   else it_rec brs
          | it_rec    []     = bug"immed_tac"
     in it_rec (Namespace.getBindings()) end;
(* ************ *)

(*** Convenient for proof by pointing ***)
fun Assumption n
    = ((message "Assumption..."; smallAppTac (immed_tac true) n))
      	handle Immed_tac => raise Error.error (Error.mkASSUMPTION n) (* *** *)

(** Immed [] is successful if at least one goal could be resolved. We
    check on progress by flagging successful exit of immed_tac and then
    checking the flags at the end -JHM 2009.12.09 **)

fun immed l =
    (message"Immediate";
     if null l (* only this branch available at top-level *)
	 then let (* JHM, 1990: start from the last goal, not the first... *)
		  val visible_goals = List.rev (Namespace.current_goal_indexes()) 
(***)		  val flags = List.map (immed_tac false) (visible_goals)
	      in
		  if List.exists (fn b=>b) flags 
(***)		     then () (* we are happy: Immed did do some work!*)
(***)		  else raise Error.error (Error.mkIMMED) (* *** none done *** *)
	      end
     else (* this branch appears can raise Failure/Error.mkIMMED *) 
      ( prs"immed cons branch" ; (* rare!!! but interesting *)
     	(List.app 
	  (fn (n,s) => RefineAutoTac_c n 0 (Engine.mkRef_c s)) (* ??? *) 
	    l handle _ => raise Error.error (Error.mkIMMED)
     	) 
      )
     );

(* 2011: changed type signature, as only top-level call available in grammar *)

fun Immed () = smallAppTac immed [];

end (* local *)

end (* struct *)
