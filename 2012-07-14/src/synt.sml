(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

functor FunSynt ( 
	structure Term : TERM
   	structure Subst : SUBST 
   	structure UMopen : UMOPEN
   	structure Toc : TOC
   	structure ParTm : PARTM
   	structure Namespace : NAMESPACE
	structure Engine : CONSTRUCTIVEENGINE
	structure Pretty : PRETTY 
   	sharing 
      		type Term.cnstr 
		   = Subst.cnstr 
		   = UMopen.cnstr 
		   = Toc.cnstr 
		   = ParTm.cnstr 
		   = Namespace.cnstr 
		   = Engine.cnstr 
		   = Pretty.cnstr 
 	and
		type Namespace.context 
		   = Engine.context 
		   = Pretty.context 
 	and
		type Subst.substitution 
		   = ParTm.substitution 
		   = Namespace.substitution 
		   = Engine.substitution 
	)
(* *** *
structure Synt
 * *** *) 
	: SYNT =

struct

val resolve_debug = ref false;
val Resolve_debug = ref false;

	type cnstr   = Engine.cnstr
	type cnstr_c = Engine.cnstr_c

  	type goals = Namespace.goals

  	type autotac = (goals -> unit) 

	exception Solve (* "doesn't solve goal" *)

        val nullTac = fn (gs:goals) => ()						

(* The principal function: try to solve the current goal against the
 * (type of) v_c.  The match is first tried against the entire TYP.
 * If that fails, TYP is progressively unwound (by explicit). *)

local

        val failwith = Utils.Except.failwith 
        val repeat = Utils.FunUtil.Repeat  

	val prs = Printing.prs

(*!*)	val prnt_goals = Pretty.prnt_goals o List.map (Namespace.unGoal) o Namespace.unGoals
	val prnt_vt = Pretty.prnt_vt
	val print_expand = Pretty.print_expand
	val print_refine = Pretty.print_refine


	open Term 

	val sub = Subst.sub
	val subst1 = Subst.subst1

	val compose = Subst.compose
	val composeSub1 = Subst.composeSub1 o Subst.mkAssign 

	val par_unif0 = ParTm.par_unif0

  exception Explicit of cnstr * cnstr;
  (* unroll a construction to make a refinement rule of it.
   * maintain invariant a achieves c with Namespace.subgoals newVars
   * (see resolve).
   *)

  fun resolve_debug_report msg (VT as (V,T)) = 
     if (!resolve_debug) then (prs msg; prnt_vt VT)
     else()

  fun explicit mkVar (a,c) =
    case UMopen.UMwhnf c
      of Bind((Pi,v),_,d,e) => let val V = mkVar d
			       in  (MkApp((a,[V]),[prVis v]),subst1 V e)
			       end
       | _ 		    => raise Explicit(a,c);

  fun resolve_abstract explicit VT (p,c) =
    let
      fun resolve_rec (ac as (a1,c1)) =
	let
(*	  val _ = if (!resolve_debug) then (prs"*res1* "; prnt_vt ac)
		  else () *)
	   val _ = resolve_debug_report "*res1* " ac
	in case par_unif0 c1 c of
	   	SOME(s) => composeSub1 (p,sub s a1) s (*compose sub [(p,sub s a1)] s*)
	      |	NONE 	=> resolve_rec (explicit (a1,c1))
	end
    in
      resolve_rec VT handle Explicit(_) => raise Solve (* failwith"doesn't solve goal" *)
    end

(* moved to NAMESPACE 2011 only used in Synt.resolve_{a,c} *

  val subPrfCxt : substitution -> context -> context 

  fun subPrfCxt s (nsp as (b::l)) =
        if sameRef b (Namespace.topContextBeforeProof()) then nsp
       else ref_updat_vt b (pair_apply (sub s) (ref_vt b))::(subPrfCxt s l)
    | subPrfCxt s [] = bug"subPrfCxt"

 * ******************************************************* *)

  fun type_of_Var_restricted m n = (* don't self-reference *this* goal *)
    if m = n then failwith("use of ?"^(Int.toString m)^" out of scope")
             else Namespace.type_of_Var n;


  fun Resolve_debug_report prftrm = 
     if (!Resolve_debug) then (print_expand prftrm)
     else()

  fun resolve_c n m v_c =      (* when v_c is a concrete term *)
    let val (mkVar,eraseNew,close) = Namespace.manageVars()
      val (l,q) = Namespace.goals()
      val goal as (n,_) = Namespace.unGoal (Namespace.goaln n)
      val ((VT as (V,T)),sbst) =
	Engine.EvalRefine_ (type_of_Var_restricted n) mkVar v_c
(*    val _ = if (!resolve_debug) then (prs"*resc1* "; prnt_vt VT)
	      else() *)
      val _ = resolve_debug_report "*resc1* " VT
      val _ = eraseNew sbst
      val (VT as (V,T)) = (repeat m (explicit mkVar) VT
			   handle Explicit(_) => failwith"too much cut")
(*    val _ = if (!resolve_debug) then (prs"*resc2* "; prnt_vt VT)
	      else() *)
      val _ = resolve_debug_report "*resc2* " VT
      val s = resolve_abstract (explicit mkVar) VT goal 
      val new = eraseNew s
(*    val _ = (message"New goals:" ; prnt_goals new) *)
      val prftrm = sub s (Namespace.getProofTerm())
(*    val _ = if (!Resolve_debug) then print_expand prftrm else () *)
      val _ = Resolve_debug_report prftrm

    in  (Namespace.subPrfCxt s (* subPrfCxt s (Namespace.getNamespace()) *),
	 new,
	 prftrm,
	 Namespace.Unknown(Namespace.erase_replace s n new l)::(Namespace.eraseq s q),
	 close,
	 V)
    end

  fun resolve_a n m V =      (* when V is an abstract term *)
    let val (mkVar,eraseNew,close) = Namespace.manageVars()
      val (l,q) = Namespace.goals()
      val goal as (n,_) = Namespace.unGoal (Namespace.goaln n)
      val T = Toc.type_of_constr V
      val VT = (V,T)
(*    val _ = if (!resolve_debug) then (prs"*resa1* "; prnt_vt VT)
	      else() *)
      val _ = resolve_debug_report "*resa1* " VT
      val (VT as (V,T)) = (repeat m (explicit mkVar) VT
			   handle Explicit(_) => failwith"too much cut")
(*    val _ = if (!resolve_debug) then (prs"*resa2* "; prnt_vt VT)
	      else() *)
      val _ = resolve_debug_report "*resa2* " VT
      val s = resolve_abstract (explicit mkVar) VT goal
      val new = eraseNew s
(*    val _ = (message"New goals:" ; prnt_goals new) *)
      val prftrm = sub s (Namespace.getProofTerm())
(*    val _ = if (!Resolve_debug) then print_expand prftrm else () *)
      val _ = Resolve_debug_report prftrm

    in  (Namespace.subPrfCxt s (* subPrfCxt s (Namespace.getNamespace()) *),
	 new,
	 prftrm,
	 Namespace.Unknown(Namespace.erase_replace s n new l)::(Namespace.eraseq s q),
	 close,
	 V)
    end

(*
      val _ = prs("\nGoal "^(Int.toString n)^" as input\n")
      val _ = prs("\nGoal "^(Int.toString n)^" as output\n") 
 *)

  fun resolve_s n m v_c =      (* when v_c is a concrete term *)
    let val (mkVar,eraseNew,close) = Namespace.manageVars()

      val goal as (n,_) = Namespace.unGoal (Namespace.goaln n)
      val ((VT as (V,T)),sbst) =
	Engine.EvalRefine_ (type_of_Var_restricted n) mkVar v_c
(*    val _ = if (!resolve_debug) then (prs"*resc1* "; prnt_vt VT)
	      else() *)
      val _ = resolve_debug_report "*resc1* " VT
      val (VT as (V,T)) = 
	(eraseNew sbst;
	 (repeat m (explicit mkVar) VT
	  handle Explicit(_) => failwith"too much cut"))
(*    val _ = if (!resolve_debug) then (prs"*resc2* "; prnt_vt VT)
	      else() *)
      val _ = resolve_debug_report "*resc2* " VT
      val s = resolve_abstract (explicit mkVar) VT goal 
      val new = eraseNew s
(* *** *
(*    val _ = (message"New goals:" ; prnt_goals new) *)
      val prftrm = sub s (Namespace.getProofTerm())
(*    val _ = if (!Resolve_debug) then print_expand prftrm else () *)
      val _ = Resolve_debug_report prftrm
 * *** *)
    in  (s,
	 n,
	 new,
	 close,
	 V)
    end

(* all the Namespace really needs is the substitution s, and the close() operation *)
(* so how do we ensure that Namespace.solve is passed a valid substitution ??? *)

in 

local 

(* solve: the main function! *)

   (* solve expects the following arguments: *
    * ************************************** *
    * 
    * tacflg : true means we want undo history and prf feedback output
    * 	       false means do nothing
    * 
    * g	     : the goal number operated upon
    * 
    * nsp    : the supposed correct new context (written en bloc! bulk load/store!)
    * 
    * new    : what new subgoals got generated? (recoverable from Namespace.current_goals()?)
    * 
    * c	     : the supposed correct current proof term
    * 
    * qs     : the supposed correct resulting proof state to return
    * 
    * close  : cf. Namespace.manageVars: fn to tidy up metavars/indexing/gensym
    * 
    * V	     : the (abstract) term we refined goal g with
    * 
    * tac    : the tactic to run on the resulting toplevel subgoals, to "tidy up"
    * 
    * ************************************** *)

      fun solve tacflg g (nsp,new,c,qs,close,V) tac =
         (if tacflg
	 	then ()
	  else (print_refine g V; Namespace.pushHist(); ());
		    
	  (*** These are UNSAFE and should be integrated in namespace.sml ***)
	       Namespace.putNamespace nsp;
	       Namespace.putProofTerm c;
	       Namespace.putCurrentQuest qs;
					
	  close(); (tac new); ()
	  );
  
      fun solved g (res as (_,gs,_,_,_,_)) = if Namespace.noMoreGoals gs 
      	  	   	   		       then (solve true g res nullTac; true)
      	  	   	   		     else false (* raise Solve *)

in

   fun Solve_s tacflg n m v_s = Namespace.solve tacflg (resolve_s n m v_s)
       	       	      	      	
   fun Solve_a tacflg n m v_a = solve tacflg n (resolve_a n m v_a)
       	       	      	      	
   fun Solve_c tacflg n m v_c = solve tacflg n (resolve_c n m v_c)
       	       	      	      	
   fun SolveImmed n m v_c = (solved n (resolve_c n m v_c) handle _ => false)

(* 2011 NEW: encapsulate the unsafe operations once and for all! *)

   fun Solve_s tacflg n m v_c = Namespace.solve tacflg (resolve_s n m v_c)
       	       	      	      	
   fun SolveImmed_s n m v_c = Namespace.solved (resolve_s n m v_c) handle _ => false

end; (* local solve *)

end; (* local everything else *)

end; (* struct *)
