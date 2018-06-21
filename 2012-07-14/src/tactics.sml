(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* 
   tactics 
   $Log: tactics.sml,v $
   Revision 1.10  1997/11/24 11:01:59  tms
   merged immed-may-fail with main branch

   Revision 1.9  1997/08/25 11:00:22  tms
   Immed fails if no progress has been achieved

   Revision 1.8  1997/07/11 13:29:24  tms
   Qrepl will fail if the LHS does not occur in the goal

   Revision 1.7  1997/07/02 16:03:17  rap
   esUMopen.sml: better diagnostics for "sameTerm" (* now: Umachine.sml *)
   tactics.sml: random changes: no change to functionality I hope!

   Revision 1.6  1997/05/28 10:35:11  tms
   Tactic Assumption prints out identification

   Revision 1.5  1997/05/08 13:42:56  tms
   added support for adding tactics

   Revision 1.4  1997/02/17 17:43:08  tms
   o reimplemented Assumption so that it aborts with
       an error message if unsuccessful

   o internal immed_tac function can now be configured to raise the
        exception Immed_tac if no progress has been achieved
*)

functor FunTactics 
	(
	structure Term:TERM
	structure Subst:SUBST
	structure Abst:ABST
	structure UMopen:UMOPEN
	structure Unif:UNIF
	structure Toplevel:TOPLEVEL
	structure Namespace:NAMESPACE
	structure Concrete:CONCRETE 
	structure Engine:CONSTRUCTIVEENGINE
	structure Pretty:PRETTY 
	structure Error:ERROR 
	sharing 
		  type Term.cnstr 
		     = Subst.cnstr 
		     = Abst.cnstr 
		     = UMopen.cnstr 
		     = Unif.cnstr 
		     = Namespace.cnstr 
		     = Concrete.cnstr 
		     = Engine.cnstr 
		     = Pretty.cnstr 
		     = Error.cnstr 
	and 	  
	 	  type Concrete.cnstr_c 
		     = Engine.cnstr_c 
		     = Toplevel.cnstr_c 
	and 	  
	 	  type Subst.substitution 
		     = Unif.substitution 
		     = Namespace.substitution 
		     = Concrete.substitution 
	)
(* *** * 
structure Tactics
 * *** *)
	: TACTICS  = (* push defn of tactic to TOPLEVEL *)
struct

val repl_debug = ref false

   type cnstr_c = Concrete.cnstr_c

   type tactic = unit -> unit 

   fun mkTactic tac = tac
   fun execute  tac = tac ()

local 
      val failwith = Utils.Except.failwith
      val bug = Utils.Except.bug

      exception Assoc = Utils.ListUtil.Assoc

      val assoc = Utils.ListUtil.assoc
      val prune = Utils.ListUtil.prune 

      val prs = Printing.prs
      val pri = Printing.pri 
      val prsp = Printing.prsp
      val message = Printing.message 

      val legoprint = Pretty.legoprint  
      val print_qrepl = Pretty.print_qrepl 
      val prnt_vt = Pretty.prnt_vt 

      open Term

      val var_occur = Term.var_occur 

      val unSubst = Subst.unSubst

      val abst = Abst.abst

      val type_match = UMopen.UMtype_match

      val type_match_unif0 = Unif.type_match_unif0 

in 


(* *** 2011 *** 

 * Configure Qrepl can be given suitable parameters for user-defined equality *
 * while vanilla Qrepl expects Q to be defined as Leibniz equality by Logic   * 
 * so, to 'improve' the modularity of all this: 

   change the '= ""' test to be on the "subst" name (Leibniz doesn't have one)
   move the particular choice of names for Leibniz to the grammar 
      (tying the grammar to Logic, but it already is...)
   initialise params to all Bot_c
   retain (for now) the peculiar switch on Bot_c to determine the substitution operator (yuk)
      (better: define a "Q_Subst" for Leibniz... )

 * ***      *** *)

(* a replace-by-equality tactic *)
local

  val equality_data = {typeName     = Concrete.Bot_c, 
		       substitution = Concrete.Bot_c, 
		       symmetry     = Concrete.Bot_c}
  val params = ref equality_data

(* 2011 version *)
  fun substitution_operator u =
      let val subst = #substitution(!params)
      in  

	(* if subst = Bot_c then u else App_c(ShowNorm,subst,u) *)

	(if (Concrete.isBot subst) then u else Concrete.mkApp_c(subst,u))

	(* if leibniz, then subst is equality itself; otherwise, need to apply it *)

      end

in

  fun Config_Qrepl (cfgdata as (tn,subst,sym)) =
    (params:= {typeName     = Concrete.mkRef_c tn, 
	       substitution = if subst = "" (* expects Logic to be loaded *)
		 	      	 then Concrete.Bot_c 
			      else Concrete.mkRef_c subst,
	       symmetry     = Concrete.mkRef_c sym};
     Namespace.addConfig ("Qrepl",cfgdata) ; (* 2011 *)
     message"'Qrepl' configured")

  fun Qreplace n v_c =
    let
 (* the conditional equation is the type of v_c *)

      val (VT as (V,T)) = Engine.EvalRefine0 (* 2011 *) v_c

      fun replErr msg = (message"Replace error:"; prnt_vt VT; failwith msg)

 (* split into conditions and equation.
  * Note the equation may not depend on the conditions,
  * but the conditions may depend on other conditions. *)

      val (nbr_conditions,equation) =
	let
	  fun conds (n,ceq) =
	    case ceq   (** this doesn't work right; need (whnf ceq), but
                        *  then reduces too far in case of leibniz *)
	      of Bind((Pi,_),_,S,U) => conds(n+1,U)
	      | eqn as (App _) =>
		  ((n, lift (~n) eqn)
		   handle Lift => replErr "equation depends on conditions")
	      | _ => replErr "not a conditional equation"
	in conds (0,T)
	end

      val _ = if (!repl_debug)
		then message("*rpl-nbr_conds* "^Int.toString nbr_conditions)
	      else ()

 (* make a concrete template for the equation *)
      val tpl_c = Concrete.mkLift_c(
			Concrete.mkLift_c(
			      Concrete.mkLiftForce_c (#typeName(!params))))

 (* compute the abstract template and find out
  * which variables are in which positions *)

      fun no_metavars n = bug("replaceER: found metavar "
      	  	      	      ^(Int.toString n)
	     	      	      ^"; metavars not allowed here"):cnstr

      fun AS_IT_WAS n   = bug("replaceER "^Int.toString n):cnstr

      val (mkVar,_,close) = Namespace.manageVars()

      val ((tpl as (App((_,[Var(TTn,_),Var(lhsn,_),Var(rhsn,_)]),_)),_),_) =
	Engine.EvalRefine_ (* no_metavars *) AS_IT_WAS mkVar tpl_c (* 2011 *)
	handle Match => bug"replace;tpl"

      val _ = if (!repl_debug) then (prs"*rplt* ";
				     pri TTn; prs" ";
				     pri lhsn; prs" ";
				     pri rhsn; prs"\n")
	      else ()
      val _ = close()

 (* unify equation with abstract template to verify
  * it is an equation, and get the types of the lhs and rhs *)
      val bngs = case type_match_unif0 equation tpl
		   of SOME(bngs) => unSubst bngs
		    | NONE => replErr"not the expected equality"
      val _ = if (!repl_debug)
		then List.app (fn (n,c) => (prs"*rpl*"; prsp();
					    pri n; prsp(); legoprint c))
		             bngs
	      else ()
      (* next binding is written to be independent of order
       * unification solves variables *)
      val [TT,lhs,rhs] = List.map (fn v => assoc v bngs) [TTn,lhsn,rhsn]
	handle _ => bug"computing lhs and rhs of equation"
      val (nn,goal) = Namespace.unGoal (Namespace.goaln n) 

(*
      fun make_abstrn k goal = (* modified Machine.subst2 *)
	if UMopen.UMtype_match lhs goal then Rel k  (*** par_tm ? ***)
	else case goal
	       of App b => umkApp (make_abstrn k) b
		| Bind b => umkBind make_abstrn k b
		| Tuple b => umkTuple (make_abstrn k) b
		| CnLst b => umkCnLst (make_abstrn k) b
		| Proj c => umkProj (make_abstrn k) c
		| RedTyp c => umkRedTyp (make_abstrn k) c
		| LabVT b => umkLabVT (make_abstrn k) b
		| x => x
      val pre_abstrn = make_abstrn 1 goal
 *)
      val pre_abstrn = abst (type_match lhs) goal
      val _ = if (var_occur pre_abstrn) then ()   (* check lhs occurs in goal *)
	      else (raise Error.error (Error.mkREPLLHS nn lhs)) (* *** *)

(*      val ZZZ = "z" (* 1998/2008: *** bug! choice of "z" *** *) *)

      val ZZZ = Namespace.mkNameGbl "z" (* 2011 *** corrected *** *)
      val abstrn = Bind((Lda,Vis),ZZZ,TT,pre_abstrn) (* lifted ZZZ out *)
      val _ = if (!repl_debug) then legoprint abstrn else ()

      fun refine n v_c = (Toplevel.RefineTac_c n 1 v_c;
			  print_qrepl V lhs rhs)
(* 1998 version *
      fun substitution_operator u =
	let val subst = #substitution(!params)
	in  

	(* if subst = Bot_c then u else App_c(ShowNorm,subst,u) *)

	(case subst of Concrete.Bot_c => u | _ => Concrete.mkApp_c(subst,u))

	(* if leibniz, then subst is equality itself; otherwise, need to apply it *)

	end
 *)

 (* make conditional equation into an equation by applying it to
  * the right number of unknowns *)
      val equation =
	let fun mk_equation 0 = v_c
	      | mk_equation n =
		if n>0
		  then Concrete.mkLiftForce_c (mk_equation (n-1))
		else bug"mk_equation"
	in  mk_equation nbr_conditions
	end

      val refterm = Concrete.mkApp_c(substitution_operator 
		    			(Concrete.mkApp_c(#symmetry (!params),equation)),
				     Engine.unEval abstrn)
    in

       Toplevel.smallAppTac (refine n) refterm

    end
end

(** Support for domain-specific tactics added by users **)

(* database of user-defined tactics: an association list *)
local 
      val UTACDB = ref [] : (string*tactic) list ref

      fun tacmsg id msg = message("UserTac "^id^msg)

      val err = ": not found!"
in 

   fun init_tactics () = (UTACDB:=[])

   fun add_tactic id f = UTACDB:=(id,f)::(!UTACDB)

   fun ExecUserTac id = let 
       		      	    val msg = tacmsg id
			in 
       		      	  (let 
       		      	       val tac = assoc id (!UTACDB)
       		      	       val exe = " ...executing: "
       		      	   in 
			      ((msg exe); execute tac)
			   end handle Assoc => msg err)
			end
    
   fun remove_tactic id = UTACDB := prune id (!UTACDB)

end (* local *)

end (* topmost local *)

end; (* struct *)
