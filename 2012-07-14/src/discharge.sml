(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* discharge.sml *)

(** Commands to DISCHARGE an assumption; to FORGET assumptions;
 ** and to CUT an assumption to a particular witness 
 **)

(* *** this makes a destructive update on NSP; can it be weakened? *** *)
(* *** currently, it implements the following rule:

       Gamma |- M:A, Gamma, x:A, Delta |- N:B
       ---------------------------------------
	Gamma, Delta[x:=M] |- N[x:=M]:B[x:=M]

 * *** when it could/should implement the following?

       Gamma |- M:A, Gamma, x:A, Delta |- N:B
       ---------------------------------------
	Gamma, [x:=M:A], Delta |- N:B

 * *** *)

(* this relies on a concrete context to cut with: but if it exists already, we * 
 * have elaborated it somewhere, so there should be sthing abstract we can use *)

functor FunDischarge(
	structure Term : TERM
   	structure Context:CONTEXT
	structure Subst : SUBST 
   	structure ParTm : PARTM
	structure Namespace:NAMESPACE
	structure Engine:CONSTRUCTIVEENGINE
     	sharing 
      		type Term.cnstr 
		   = Context.cnstr 
		   = Subst.cnstr 
		   = ParTm.cnstr 
		   = Namespace.cnstr 
		   = Engine.cnstr 
     	and 
		type Term.binding
		   = Context.binding
		   = Subst.binding
		   = Namespace.binding
     	and 
		type Context.context
		   = Namespace.context
		   = Engine.context
     	and 
		type Subst.substitution
		   = ParTm.substitution
		   = Namespace.substitution
		   = Engine.substitution
	)

(* *** * 
structure Discharge 
 * *** *)
	: DISCHARGE 
 = 

struct

	type cnstr_c = Engine.cnstr_c

(* Cut: to specialize declarations *)
(* Ref's should have ts of their referent, NOT the value! *)

local 

	val failwith = Utils.Except.failwith

	open Utils.Modif 

	val message  = Printing.message 

	open Term  

	val addBndCxt = Context.addBndCxt
	val unDefined = Context.unDefined
	val splitCxt  = Context.splitCxt
	val mkCxt     = Context.mkCxt
	val unCxt     = Context.unCxt

	val mkSubst1	   = Subst.mkSubst1
	val sub_Ref_pr	   = Subst.sub_Ref_pr
	val composeSubRef1 = Subst.composeSubRef1 o Subst.mkAssign
	val expandRef 	   = Subst.expandRef_as_needed 

	val par_tm = ParTm.par_tm 

   fun unsplit_subRef s (new,old) =
      case new
	of (br::rest) =>
	  let 
	      val vt = ref_vt br
	      val ts = ref_ts br
(* 2011 version *)
	      val (newbr,news) =
		case sub_Ref_pr s vt
		  of   UMod    => (br,s)
		   | (Mod vt') => let 
				      val newbr = ref_updat_vt br vt'
		     	       	  in  
				      (newbr,composeSubRef1 (ts,Ref newbr) s)
				  end 
(* ************ *)
(* 1998 version *
	      val (newbr,chg_flg) =
		case sub_Ref_pr s vt
		  of   UMod    => (br,false)
		   | (Mod vt') => (ref_updat_vt br vt',true)
	      val news = if chg_flg
			   then composeSubRef1 (ref_ts br,Ref newbr) s
			 else s
 * ************ *)
	  in  unsplit_subRef news (rest,newbr::old)
	  end
	 |    []      => mkCxt old;

   fun cut ((lft,rht),cxt) = (* 2011: List.foldl *)
      let
	val rv = Engine.fEvalVal rht

	val (hit,new,old) = (* splitCxt in Context *)
	  splitCxt (mtnNam lft) (lft^" undefined") cxt

(* 2011 *) 
   	val _ = if (ref_isDecl hit)
		   then ()
		 else failwith("LHS of Cut is a definition: "^lft)

	fun fresh_for_old br = unDefined (ref_nam br) old 

(* 
        fun expand_as_needed cxt = expandRef_as_needed (fn br => unDefined (ref_nam br) cxt)
(* 
	  fn (rbr as (Ref br)) =>
                    if ref_isDefn br andalso (unDefined (ref_nam br) cxt)
		      then (expand_as_needed cxt) (ref_VAL br) else rbr
	   | (App b)   => umkApp   (expand_as_needed cxt) b
	   | (Bind b)  => umkBind2 (expand_as_needed cxt) b
	   | (Tuple b) => umkTuple (expand_as_needed cxt) b
	   | (CnLst b) => umkCnLst (expand_as_needed cxt) b
	   | (Proj b)  => umkProj  (expand_as_needed cxt) b
	   | (RedTyp b)=> umkRedTyp (expand_as_needed cxt) b
	   | x         => x
 *)
 *)

	val (rv,rt) =
(* 	  Engine.fEvalCxt old (Engine.unEval (expand_as_needed old rv)) *)
	  Engine.fEvalCxt old (Engine.unEval (expandRef fresh_for_old rv))


(* 2011 *) 
	val t = ref_typ hit
   	val _ = if (par_tm rt t)     (******  better msg *****)
		   then ()
		 else failwith("type does not match in Cut: "^lft)
		
	val ts = ref_ts hit
	val cut_hit = ref_promote_to_def hit lft (rv,t) 

(* 1998 *
	val (ts,param,deps,t) =
	  case hit
	    of Bd{ts,param,deps,bd=(_,_,t,_),...}
	      => if not (ref_isDecl hit)
		   then failwith("LHS of Cut is a definition: "^lft)
		 else if not (par_tm rt t)    (******  better msg *****)
		   then failwith("type does not match in Cut: "^lft)
		 else (ts,param,deps,t)

	val param = loc2glob param

	val cut_hit = Bd{kind=Bnd,ts=ts,frz=ref UnFroz,param=param,deps=deps,
			 bd=(LetDef,lft,rv,t)}
 *)

      in 
      	 (message("Cut "^lft);
	  unsplit_subRef (mkSubst1(ts,Ref cut_hit)) ((unCxt new),cut_hit::(unCxt old)))
      end;
in 
    
fun Cut cc =
  let
     (* everything lifted out as locals above *)
     (* 2011: should we run MakeAllPats after updating NSP? *)
  in 
     Namespace.putNamespace (List.foldl cut (Namespace.getNamespace()) cc)

  end;

end; (* local *)
end; (* struct *)
