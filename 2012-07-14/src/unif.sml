(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* unif.ml *)

(* WARNING: In the future, if bindings can ever mention ex-vars then
 * many things in this file need to be re-thought.
 *)

functor FunUnif (structure Term : TERM
		 structure Subst : SUBST
		 structure UMopen : UMOPEN
		 structure Toc : TOC
		 structure Pretty : PRETTY
		 sharing 
		   	   type Term.cnstr
			      = Subst.cnstr
			      = UMopen.cnstr
			      = Toc.cnstr
			      = Pretty.cnstr
		 and 
		   	   type Term.binding
			      = Subst.binding
			      = Pretty.binding
		 ) 
(* *** *
structure Unif 
 * *** *)
	: UNIF 
  = 
struct
(* 
 *)

local

      val bug = Utils.Except.bug 

      val succ = Utils.Counting.succ

      open Utils.Modif   

      val prs = Printing.prs
      val message = Printing.message

      val legoprint = Pretty.legoprint
      val print_expand = Pretty.print_expand
(*  *)
      fun chop_list n l = (List.take(l,n), List.drop(l,n))

      open Term  

      open Subst  

      fun liberal() = !UMopen.liberal_matching_switch

      val whnf = UMopen.UMwhnf
      val unifwhnfP = UMopen.unifwhnfP
      val rUMwhnf = UMopen.rUMwhnf
      val s1UMwhbenf = UMopen.s1UMwhbenf

      val toc = Toc.type_of_constr

in

	type cnstr = Term.cnstr

	type assignment = Subst.assignment 
	type substitution = Subst.substitution

(* *)
val unif_debug = ref false;
val whun_debug = ref false;

fun unif_debug_print (msg:string) prntr M = 
    if (!unif_debug) 
       then (prs msg;prntr M)
    else ();

fun unif_debug_report msg = unif_debug_print "" message msg 

fun whun_debug_print (msg:string) prntr M = 
    if (!whun_debug) 
       then (prs msg;prntr M)
    else ();

(* iterative deepening parameters *)
val unif_start_dpth = ref  50;
val unif_deepen_factor = ref 2;

(** forward reference to par_tm: moved to ParTm in cml.sml * 
val r_par_tm = ref(fn x:cnstr => fn y:cnstr => false);
 *)

(** unification **)

local 

    exception Unif;     (* fail: different structure *)

    val clean =
	  fn Bot       => bug"whun;clean Bot"
	   | RedTyp(_) => bug"whun;clean RedTyp"
	   | CnLst(_)  => bug"whun;clean CnLst"
	   | LabVT(_)  => bug"whun;clean LabVT"
	   | 	 c     =>  c


 in 

(* uniflg=true for unification;
 * false for heuristic type matching (failing on any Var)
 *)

fun Unirec uniflg s (M,N) =
  let
    exception unif
    exception unifVar  (* fail: variable is found (heuristic type matching) *)
    val DpthExceeded = ref false

    fun unirec LMflg (Dpth as (dpth,maxd)) s (MN as (M,N)) =
      let

        fun debPrtDpth s = (Int.toString dpth)^" "^(Int.toString maxd)^" "^
                           (Bool.toString (!DpthExceeded))^" "^s

 	fun raiseUnif (s,(m,n)) = 
	  (unif_debug_report ("**raiseUnif* "^debPrtDpth s);
	   unif_debug_print "" print_expand m;
	   unif_debug_print "" print_expand n;
	   raise unif);

	val _ = if dpth<=maxd then ()
                else (DpthExceeded:= true; raiseUnif("dpth ",MN))

        val unirec_cumul = unirec LMflg (succ dpth,maxd) 

        val unirec_equal = unirec false (succ dpth,maxd) 

	fun uniargs s args1args2 = (* 2011: List.foldl *)
	  let fun uabod (mn,s) = unirec_equal s mn 
	  in  List.foldl uabod s (ListPair.zipEq args1args2 handle _ => bug"uniargs")
	  end (* 2011: List.foldl *)

        (* fun handleUnif an = UVARS:= an (* *** *) *)

	fun reunion (p,P) M =
	  (* we guarantee that p is not bound in s, but M may be a meta-var.
	   * p and M may be the same meta-var, but that is not an occur check
	   *)
	  let
	    val ov = free_occur M
	    val mv = mv_occur p M
	  in
	    if mv orelse ov
	      then raiseUnif
		(("reunion: "^(if mv then "occurs check" else "free o-var")),
		 (Bot,Bot))
	    else let val tM = toc M
		     val s = Unirec uniflg s (tM,P)
                             handle Unif => raise unif
		 in composeSub1 (mkAssign(p,M)) s (*compose sub [(p,M)] s*)
		 end
	  end

	fun progWhnf c =     (* all the way to whnf *)
	  (unif_debug_print "** unif_deb; whnf: " legoprint c; 
	   if (!unif_debug) 
	      then (prs"** unif_deb; whnf: "; Pretty.legoprint c)
	   else ();
	   case rUMwhnf c 
	     of UMod => raiseUnif("backtrack:no change on reduction",(Bot,Bot))
	      | Mod(c) => c)

	fun try_approx MN =
	  let
	    val MN as (M,N) = sub_pr s MN

	    fun eagerP x =  (* this is entirely heuristic: what is good
			     * to reduce more eagerly than definitions:
			     * higher numbers are more eager *)
	      case x of
		App((Bind((Lda,_),_,_,_),_),_) => 10
	      | Proj(Fst,Tuple _) => 10
	      | Proj(Snd,Tuple _) => 8
	      | Bind((Let,_),_,_,_) => 12
	      | _ => ~1                (*  neg means no eager contraction *)
	    local
	      fun ur mn = unirec_cumul s mn
	      fun first flg stopTS =
		let
		  exception ta
		  fun exp1 tmplt c =
		    case s1UMwhbenf stopTS c
		      of Mod(c') => tmplt c'
		       | UMod => (case s1UMwhbenf ~1 c
				    of Mod(c') => tmplt c'
				     | UMod => raise ta)
		  fun expM() = exp1 (fn c => ur (c,N)) M
		  fun expN() = exp1 (fn c => ur (M,c)) N
		in
		  if flg then
		    let 
		    	val _ = unif_debug_report "**unif_debug: firstM"
		    in  expM() handle ta =>
		        expN() handle ta =>
			raiseUnif("backtrack",MN)
		    end
		  else
		    let 
		    	val _ = unif_debug_report "**unif_debug: firstN"
		    in  expN() handle ta =>
		        expM() handle ta =>
			raiseUnif("backtrack",MN)
		    end
		end
	    in
	      val firstM = first true
	      val firstN = first false
	      fun both() =
		case (s1UMwhbenf ~1 M,s1UMwhbenf ~1 N)
		  of (Mod M,Mod N) => ur (M,N)
		   | (Mod M, UMod) => ur (M,N)
		   | (UMod, Mod N) => ur (M,N)
		   | (UMod,  UMod) => raiseUnif("backtrack",MN)
	    end
	    fun onlyM() = unirec_cumul s (progWhnf M,N)
	    fun onlyN() = unirec_cumul s (M,progWhnf N)
	  in
	    case (unifwhnfP M, unifwhnfP N)
	    	 (* (whnfP unifDfnFlgs M,whnfP unifDfnFlgs N) *)
	      of (true,true) => raiseUnif("backtrack: both are pwhnfs",MN)
	       | (false,true) => onlyM()   (* direct to whnf *)
	       | (true,false) => onlyN()   (* direct to whnf *)
	       | (false,false) =>
		   (case (eagerP M,eagerP N) of
		      (~1,~1) =>
			(case MN of
			   (App((Ref bM,_),_),App((Ref bN,_),_)) =>
			     let val tsM = ref_ts bM
			         val tsN = ref_ts bN
			     in  if tsM<tsN then firstN tsM
				 else firstM tsN
			     end
			 | _ => firstM ~1)
		    | (m,n) => if m>=n             (** expand both? **)
				 then firstM ~1 else firstN ~1)
	  end
(* 
	val MN as (M,N) =
	  let
	    fun clean c =
	      case c of
		Bot 	  => bug"unif;clean Bot"
	      | RedTyp(_) => bug"unif;clean RedTyp"
	      | CnLst(_)  => bug"unif;clean CnLst"
	      | LabVT(_)  => bug"unif;clean LabVT"
	      | _ =>  c
	  in  (sub s (clean M),sub s (clean N))
	  end
 *) 
        fun clarify c = sub s (clean c) 

	val MN as (M,N) = (clarify M,clarify N)

	val _ = unif_debug_report("*unif_deb,  "^debPrtDpth("uniflg "^Bool.toString uniflg))

	val _ = unif_debug_print "   " print_expand M

	val _ = unif_debug_print "   " print_expand N

	val _ = if (!unif_debug) 
	      	   then (prs("*unif_deb,  "^debPrtDpth "");
		      	 message(" uniflg "^Bool.toString uniflg);
		      	 prs"   ";print_expand M;
		      	 prs"   ";print_expand N)
		else ()
      in

	case MN of
	  (Var(mtm as (m,_)),Var(ntn as (n,_))) =>
	    if m=n then s
	    else if not uniflg then raise unifVar
		 else if m>n then reunion mtm N
		      else reunion ntn M
	| (Var(mtm),_) => if uniflg then reunion mtm N else raise unifVar
	| (_,Var(ntn)) => if uniflg then reunion ntn M else raise unifVar
	| (Type(i),Type(j)) =>
	    if (Universes.univ_cmp_ LMflg i j) (* 2011: univ_cmp_ *)
	      then s
	    else raiseUnif("Types",MN)
	| (Prop,Type(j)) => if LMflg then s else raiseUnif("Prop/Type",MN)
	| (Prop,Prop) => s
	| (Rel n,Rel m)  => if n=m then s else raiseUnif("Rel",MN)
	| (Rel m,N) =>
	    if varn_occur m N then unirec false Dpth s (M,progWhnf N)
	    else raiseUnif("Rel_Other",MN)
	| (M,Rel n) =>
	    if varn_occur n M then unirec false Dpth s (progWhnf M,N)
	    else raiseUnif("Other_Rel",MN)
	| (Ref b1,Ref b2) => (* since decls may expand by special,
			      * defns and decls are treated the same *)
	    if sameRef b1 b2 then s else try_approx MN
	| (Bind((Let,_),_,v1,b1),Bind((Let,_),_,v2,b2)) =>
	    let
	      fun expBoth() = 
		let
		  val v1 = sub s v1
		  val v2 = sub s v2
		in  unirec_equal s (subst1 v1 b1,subst1 v2 b2)
		end
	      (* val an = !UVARS (* *** *) *
	    in unirec_cumul (unirec_equal s (v1,v2)) (b1,b2)
	      handle unif => (handleUnif an; expBoth()) (* *** *)
	       *)
	    in Universes.handleUniverses (unirec_cumul (unirec_equal s (v1,v2))) (b1,b2)
	       handle unif => expBoth()
	    end
(* *************************************************** *)
	| (App((f1,cs1),vs1),App((f2,cs2),vs2)) =>
(* 1998 *)
(*	    let 
	    	val an = !UVARS (* *** *)
	    in  let
		  val l1 = length cs1 and l2 = length cs2
		  val (f1,f2,cs1,cs2) =
		    if l1 = l2 then (f1,f2,cs1,cs2)
		    else if l1 < l2 
			   then let val l2l1 = l2-l1
				    val (pre,post) = chop_list l2l1 cs2
				    val (prev,postv) = chop_list l2l1 vs2
				in  (f1,App((f2,pre),prev),cs1,post)
				end
			 else let val l1l2 = l1-l2
				  val (pre,post) = chop_list l1l2 cs1
				  val (prev,postv) = chop_list l1l2 vs1
			      in  (App((f1,pre),prev),f2,post,cs2)
			      end
		in uniargs (unirec_equal s (f1,f2)) (cs1,cs2)
		end                          (* in case of beta *)
	      handle unif => (handleUnif an;try_approx MN) (* *** *)
	    end 
 *)
(* 2011 *)
	    let 
		val l1 = length cs1 and l2 = length cs2
		val (f1,f2,cs1,cs2) =
		    if l1 = l2 then (f1,f2,cs1,cs2)
		    else if l1 < l2 
			   then let val l2l1 = l2-l1
				    val (pre,post) = chop_list l2l1 cs2
				    val (prev,postv) = chop_list l2l1 vs2
				in  (f1,App((f2,pre),prev),cs1,post)
				end
			 else let val l1l2 = l1-l2
				  val (pre,post) = chop_list l1l2 cs1
				  val (prev,postv) = chop_list l1l2 vs1
			      in  (App((f1,pre),prev),f2,post,cs2)
			      end
		
	    in  Universes.handleUniverses (uniargs (unirec_equal s (f1,f2))) (cs1,cs2)
	      	handle unif => try_approx MN           (* in case of beta *)
	    end 

	| (Bind((Pi,vs1),_,M1,M2),Bind((Pi,vs2),_,N1,N2)) =>
	    if (liberal() orelse vs1=vs2)
	      then unirec_cumul (unirec_equal s (M1,N1)) (M2,N2)
	    else raiseUnif("Pi",MN)
	| (Bind((Lda,vs1),_,M1,M2),Bind((Lda,vs2),_,N1,N2)) =>
	    unirec_equal (unirec_equal s (M1,N1)) (M2,N2)
	| (Bind((Sig,_),_,M1,M2),Bind((Sig,_),_,N1,N2)) =>
	    unirec_cumul (unirec_cumul s (M1,N1)) (M2,N2)
	| (Bind((Thry,_),_,_,_),Bind((Thry,_),_,_,_)) => bug"unif:Thry"
	| (Tuple(T1,ls1),Tuple(T2,ls2)) =>
	    if (length ls1)=(length ls2)
	      then uniargs (unirec_equal s (T1,T2)) (ls1,ls2)
	    else raiseUnif("Tuples",MN)
	| (Proj(p1,c1),Proj(p2,c2)) =>
	    if p1<>p2 then try_approx MN
	    else (case (c1,c2) of
		    (Tuple _,Tuple _) =>   (* avoid traversing canonical tuples *)
		      (let
			 val (Mod M') = s1UMwhbenf ~1 M
			 val (Mod N') = s1UMwhbenf ~1 N
		       in unirec_cumul s (M',N')
		       end handle Match => bug"unif:Proj Match")
		  | _ =>
		      (Universes.handleUniverses (unirec_equal s) (c1,c2) 
		       handle unif => try_approx MN)
		      (* let 
		      	  val an = !UVARS (* *** *)
		      in  (unirec_equal s (c1,c2))
			(* in case projection *)
			handle unif => (handleUnif an; try_approx MN) (* *** *)
		      end *)
		   )
	| (Theory,Theory) => s
	|        _  	  => try_approx MN
  end

(* 2011 *)

      fun uniTop max_dpth = 

     (Universes.handleUniverses (unirec (!Theories.LuosMode) (0,max_dpth) s) (M,N) 
      handle unif => 
      	     (unif_debug_report ("***unif caught at uniTop: "
	   		         ^Bool.toString (!DpthExceeded));
	      if (!DpthExceeded) then
	      	 let val max_dpth = max_dpth*(!unif_deepen_factor)
		     val _ = DpthExceeded:= false
		     val _ = unif_debug_report ("***max_dpth increased to "
		       	 		        ^(Int.toString max_dpth)); 
	         in  uniTop max_dpth
	     	 end
	      else raise Unif)
      	   | unifVar => (* not quite right! *) (* ??? 2011 ??? *)
	     (unif_debug_report ("***unifVar caught at UniTop");
	      raise Unif)
     )

in  

(* 1998 *)
(* 
  let val an = !UVARS     (*** !! side effects !! ***)
      fun uniTop max_dpth =
	unirec LMflg (0,max_dpth) s (M,N)
	handle unif =>
	  (UVARS:= an; (* *** *)
	   if (!unif_debug) 
	      then (message("***unif caught at uniTop: "^Bool.toString (!DpthExceeded)))
	   else ();
	   if (!DpthExceeded) then
	     let val max_dpth = max_dpth*(!unif_deepen_factor)
		 val _ = DpthExceeded:= false
		 val _ = if (!unif_debug) 
		       	    then (message("***max_dpth increased to "^
				      (Int.toString max_dpth)))
			 else ();
	     in  uniTop max_dpth
	     end
	   else raise Unif)
	     | unifVar =>
	       (UVARS:= an; (* *** *)
		if (!unif_debug) then (message"***unifVar caught at UniTop")
		else ();
		raise Unif)                           (* not quite right! *)
  in  

      uniTop (!unif_start_dpth)
  end

 *)

  uniTop (!unif_start_dpth)

end;


fun type_match_unif s M N =         (* real unification *)
  let
(* 
    val _ = if !unif_debug
	     then (message"** type_match_unif_deb **";
		   print_expand M; print_expand N)
	   else ()
 *)
    val _ = unif_debug_report "** type_match_unif_deb **";
    val _ = unif_debug_print "" print_expand M
    val _ = unif_debug_print "" print_expand N

  in  SOME (Unirec true s (M,N))
      handle Unif => NONE
  end;

val type_match_unif0 = type_match_unif nilS 

fun type_match_heur M N =         (* no variable instantiation *)
  let
(* 
    val _ = if !tm_debug
	     then (message"** type_match_heur_deb **";
		   print_expand M;print_expand N)
	   else ()
 *)

    val _ = UMopen.tm_debug_report "** type_match_unif_deb **";
    val _ = UMopen.tm_debug_print "" print_expand M
    val _ = UMopen.tm_debug_print "" print_expand N

  in  (Unirec false nilS (M,N);true)
       handle Unif => false
  end;

end; (* of local exn Unif *)

(************  partial unification first going to whnf  *************)
local 

    exception whnfunif

    val clean =
	  fn Bot       => bug"whun;clean Bot"
	   | RedTyp(_) => bug"whun;clean RedTyp"
	   | CnLst(_)  => bug"whun;clean CnLst"
	   | LabVT(_)  => bug"whun;clean LabVT"
	   | 	 c     =>  c

    fun debug_report M N = 
    	(whun_debug_print "*whun_deb " print_expand M; 
	 whun_debug_print "*         " print_expand N)

    fun unirec LMflg s (M,N) =
      let

        fun clarify c = sub s (clean (whnf c)) 

	val MN as (M,N) = (clarify M,clarify N)

	val whnf_unif_equal = unirec false
	val whnf_unif_cumul = unirec LMflg 

    	fun uniargs s args1args2 = (* 2011: List.foldl *)
	  let fun uabod (mn,s) = whnf_unif_equal s mn 
	  in  List.foldl uabod s (ListPair.zipEq args1args2 handle _ => bug"uniargs")
	  end (* 2011: List.foldl *)

    	fun reunion (p,P) M =
	  (* we guarantee that p is not bound in s, but M may be a meta-var.
	   * p and M may be the same meta-var, but that is not an occur check
	   *)
	  let
	    val ov = free_occur M
	    val mv = mv_occur p M
	  in
	    if mv orelse ov
	      then raise whnfunif
	    else let val tM = toc M (* *** !toc? *** *)
		     val s = unirec (!Theories.LuosMode) s (tM,P)
		 in composeSub1 (mkAssign (p,M)) s (*compose sub [(p,M)] s*)
		 end
	  end

      in

	case MN
	  of (Var(mtm as (m,_)),Var(ntn as (n,_))) =>
	        if m=n then s
		else if m>n then reunion mtm N
		     else reunion ntn M
	   | (Var(mtm),_) => reunion mtm N
	   | (_,Var(ntn)) => reunion ntn M
	   | (Type(i),Type(j)) =>
	       if (Universes.univ_cmp_ LMflg i j) (* 2011: univ_cmp_ *)
		 then s else raise whnfunif
	   | (Prop,Type(j)) => if LMflg then s else raise whnfunif
	   | (Prop,Prop) => s
	   | (Rel n,Rel m)  => if n=m then s else raise whnfunif
	   | (Ref b1,Ref b2) => if sameRef b1 b2 then s else raise whnfunif
	   | (App((f1,cs1),vs1),App((f2,cs2),vs2)) =>
	       if length cs1 <> length cs2 then raise whnfunif
	       else uniargs (whnf_unif_equal s (f1,f2)) (cs1,cs2)
	   | (Bind((Pi,vs1),_,M1,M2),Bind((Pi,vs2),_,N1,N2)) =>
	       if (liberal() orelse vs1=vs2)
		 then whnf_unif_cumul (whnf_unif_equal s (M1,N1)) (M2,N2)
	       else raise whnfunif
	   | (Bind((Lda,vs1),_,M1,M2),Bind((Lda,vs2),_,N1,N2)) =>
	       whnf_unif_equal (whnf_unif_equal s (M1,N1)) (M2,N2)
	   | (Bind((Sig,_),_,M1,M2),Bind((Sig,_),_,N1,N2)) =>
	       whnf_unif_cumul (whnf_unif_cumul s (M1,N1)) (M2,N2)
	   | (Bind((Thry,_),_,_,_),Bind((Thry,_),_,_,_)) => bug"whun:Thry"
	   | (Tuple(T1,ls1),Tuple(T2,ls2)) =>
	       if (length ls1)=(length ls2)
		 then uniargs (whnf_unif_equal s (T1,T2)) (ls1,ls2)
	       else raise whnfunif
	   | (Proj(p1,c1),Proj(p2,c2)) =>
	       if p1=p2 then whnf_unif_cumul s (c1,c2) else raise whnfunif
	   | (Theory,Theory) => s
	   |        _  	     => raise whnfunif
      end

in 
   fun whnf_unif s M N =

      let 
    	 val MN = (M,N)
    	 val _ = debug_report M N
    	    (* if (!whun_debug) 
    	       then (prs"**whun_deb** ";print_expand M;
		     prs"             ";print_expand N)
	       else () *)

(* 2011 *)
    	 val sbst = Universes.handleUniverses (unirec (!Theories.LuosMode) s) MN
      in  
         SOME(sbst)
      end handle whnfunif => (NONE) (* *** *)
 
(* 1998 *)
(*
    	 val an = !UVARS     (* *** !! side effects !! *** *)
      in  SOME(unirec (!LuosMode) s MN)
        handle whnfunif => (UVARS:= an; NONE) (* *** *)
      end
 *)

end; (* local decl of whnfunif, clean, debug_report *)

end; (* local decl of legoprint *)


end; (* struct *)
