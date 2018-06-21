(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* toc.ml   compute type of an closed abstract construction *)

functor FunToc (structure Term : TERM
		structure Subst : SUBST
		structure UMopen : UMOPEN
		structure Pretty : PRETTY
		sharing 
		   	   type Term.cnstr
			      = Subst.cnstr
			      = UMopen.cnstr
			      = Pretty.cnstr
		   and 
		   	   type Term.binding
			      = Subst.binding
			      = Pretty.binding
		   ) 
(* *** *
structure Toc 
 * *** *)
	: TOC  
  = 
struct

local

      exception Failure = Utils.Except.Failure 
      val failwith = Utils.Except.failwith
      val bug = Utils.Except.bug

      val assoc = Utils.ListUtil.assoc
      val nth = Utils.ListUtil.nth
      exception Nth = Utils.ListUtil.Nth

      val squote = Utils.StringUtil.squote
      val dquote = Utils.StringUtil.dquote

      val succ = Utils.Counting.succ

      val prs = Printing.prs
      val message = Printing.message

      val legoprint = Pretty.legoprint
      val prnt_vt = Pretty.prnt_vt

      val subst1 = Subst.subst1

      val whnf = UMopen.UMwhnf 
      val thryUMwhnf = UMopen.thryUMwhnf 

      open Term 
(*  *)
in

	type cnstr = Term.cnstr 

val toc_debug = ref false;

fun toc_debug_report msg prntr c = 
    if !toc_debug 
       then (prs msg;prntr c) 
    else ()

(* val toc = ref (fn (x:cnstr) => x) (* for Conor's stuff; is it needed??? *) *) 

  (* projections from Theories: shared with machine *)
fun TheoryProject lab V =
  case thryUMwhnf V of  (* theory must be in whnf to see its labels *)
    Bind((Thry,_),_,_,CnLst lvts) => 
      let 
	fun assoc (LabVT(Name l,_,A)::rest) = if l=lab then A else assoc rest
	  | assoc [] = failwith("label "^squote(lab)^" doesn't occur in Theory")
	  | assoc _ = bug"TheoryProject; assoc"
	val A = assoc lvts
      in (Proj(Labl lab,V),subst1 V A)
      end
(* ****************************** *
     | Bind(bvs as (Lda,vs),nam,lft,rht) =>    (* !!not checked!! *)
	 let val (V,T) = TheoryProject(rht,n)
	 in  (Bind(bvs,nam,lft,V),Bind((Pi,vs),nam,lft,T))
	 end
 * ****************************** *)
     | _ => (message("Cannot theory project "^dquote(lab)^" from ");
		     legoprint V;
		     failwith"Theory projection fails")
(* ****************************** * * ****************************** *)


(* Compute the type of an (abstract) construction.
 * Fix an (abstract) construction after reduction may have
 * destroyed its "visibility" incorrect
 *)

local 

	 val mkType0 = Term.mkTyp(Universes.mkUcon 0)
	 fun mkTypen n = Term.mkTyp(Universes.tocNode n)
	 fun mkTypeGe j i = Term.mkTyp(Universes.mkUvarGe j i)

  fun assume d cxt = d::cxt
  and typ n cxt = lift n (nth cxt n handle Nth _ => bug"toc: Nth raised")
  and toc cxt c = (* 2011: ???handleUniverses in the event of failure here??? *)
    let
      val t = toc_rec cxt c (* handleUniverses (toc_rec cxt) c *)
      	      handle Failure s => (* can this happen other than Bug? *)
	        (prs"\ntoc fail on: "; legoprint c; failwith s)
      val _ = if (!toc_debug) then (prs"*toc1* "; prnt_vt (c,t))
	      else()
    in t
    end
  and toc_rec cxt =
    let  (* 
    	 val whnf = UMopen.UMwhnf 
	 val type0 = mkTyp(Universes.uconst 0)
	  *)
    in 
      fn Ref(br)       => ref_typ br
       | Prop          => mkType0
       | Theory        => mkType0 
       | Type(nod)     => mkTypen nod 
(*        | Type(Uconst n)=> mkTyp(uconst (succ n))                    * 
 *        | Type(n)       => mkTyp(mkUvarGt n) (* uvar "" [UniGt(n)] *)*)
       | Var(_,c)      => c
       | Rel(n)        => typ n cxt
       | Bind((Let,_),_,v,b) => toc cxt (subst1 v b)
                      (** old:  toc (assume (toc cxt v) cxt) b   **)
       | Bind((Thry,_),_,_,_) => Theory
       | LabVT(_,_,T) => T
       | appTrm as (App((f,cs),_)) =>
	   let val _ = if (!toc_debug) then (prs"*tocApp* "; legoprint appTrm)
                       else()
             fun toa (a,ft) = (* 2011: List.foldl *)
	     let
               val whnfft = whnf ft
	       val t = 
                 case whnfft
		   of Bind((Pi,_),_,_,r) => subst1 a r
	            | _ => (prs"*tocAppErr* ";legoprint whnfft;
                            bug"toc:application of a non-function")
	       val _ = if (!toc_debug) then (prs"*tocApp1* "; legoprint t)
		       else()
	     in t
	     end
	   in List.foldl toa (toc cxt f) cs (* 2011: List.foldl *)
	   end
       | Bind((Lda,v),n,d,r) =>
	   MkBind((Pi,v),n,d,toc (assume d cxt) r)
       | Bind((Pi,_),n,d,r) =>
	   (case (whnf(toc cxt d),whnf(toc (assume d cxt) r)) 
	      of (_,Prop)          => Prop
	       | (Prop,Ti as (Type i)) => Ti
	       | (Type(j),Type(i)) => mkTypeGe j i (* uvar "" [UniGe(i),UniGe(j)] *)
	       | _                 => bug"type_of_constr;Pi")
       | Bind((Sig,_),_,d,r) =>
	   (case (whnf (toc cxt d),whnf (toc (assume d cxt) r))
	      of (Prop,Prop) => if (!Theories.AczelMode) then mkType0 (*mkTyp(uconst 0)*)
				else Prop
	       | (Prop,Ti as Type(_)) => Ti
	       | (Ti as Type(_),Prop) => Ti
	       | (Type(j),Type(i)) => mkTypeGe j i (* uvar "" [UniGe(i),UniGe(j)] *)
	       | _                 => bug"type_of_constr;Sig")
       | Tuple(T,_) => T
       | Proj(Labl(l),V) => #2 (TheoryProject l V)  (* *** where? *** *)
       (* *** 		#2 (Machine.ProjectLabel l (V, toc cxt V)) *** *)
       | Proj(p,c) =>
	   (case whnf (toc cxt c)
	      of Bind((Sig,_),_,d,r) => if p=Fst then d
					else subst1 (MkProj(Fst,c)) r
	       | _                   => bug"type_of_constr;Proj")
       | RedTyp(iNrml,c) => UMopen.UMnorm(toc cxt c)         (**** temp *****)
       | CnLst _ => bug"type_of_constr:CnLst"
       | Bot     => bug"type_of_constr:Bot"
       | _       => bug"type_of_constr: Match failure!"
    end

  val type_of_constr_ = toc []  

in

  fun type_of_constr c =
    let
      val _ = if (!toc_debug) then (prs"*toc* input "; legoprint c)
      	      else ()
      val T = type_of_constr_ c
      val _ = if (!toc_debug) then (prs"*toc* output "; legoprint T)
      	      else ()
    in  T
    end

end (* of local for type_of_constr *)

end (* of local for legoprint *)

val _ = Term.tocr:= type_of_constr   (* fix forward referencing *)

end; (* of struct *)
      
(* open Toc; *)
