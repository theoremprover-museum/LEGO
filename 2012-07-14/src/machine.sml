(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* machine.ml *)

(* needs Univ, Term, Umachine (* for whnf etc. *) *)

functor FunMachine (structure Term : TERM 
		    structure Context : CONTEXT 
		    structure Subst : SUBST 
		    structure Abst : ABST 
		    structure UMopen : UMOPEN 
		    structure Toc : TOC 
		    structure ParTm : PARTM
		    structure Pretty : PRETTY
		    structure Error : ERROR
		    sharing 
		   	   type Term.cnstr
			      = Context.cnstr
			      = Subst.cnstr
			      = Abst.cnstr
			      = UMopen.cnstr
			      = Toc.cnstr
			      = ParTm.cnstr
			      = Pretty.cnstr
			      = Error.cnstr
		    and 
		   	   type Term.binding
			      = Context.binding
			      = Subst.binding
			      = Pretty.binding
		    and 
		   	   type Context.context
			      = Pretty.context
		    and 
		   	   type Subst.substitution
			      = ParTm.substitution
		  ) 
(* *** *
structure Machine 
 * *** *)
	: MACHINE 

 =

struct 

         type cnstr = Context.cnstr
  	 type binding = Context.binding

	 type context = Context.context

	 type substitution = Subst.substitution
	
	 type Kind = Term.Kind
	 type Prefix = Term.Prefix
	 type projSort = Term.projSort
	 type bindVisSort = Term.bindVisSort
	 type prntVisSort = Term.prntVisSort
	 type frzLocGlob = Term.frzLocGlob

val mach_debug = ref false
val gen_debug = ref false

local 

      val bug = Utils.Except.bug
      val failwith = Utils.Except.failwith

      val succ = Utils.Counting.succ

      val prs = Printing.prs
      val message = Printing.message

      val legoprint = Pretty.legoprint
      val prnt_vt = Pretty.prnt_vt
      val prnt_vt_expand = Pretty.prnt_vt_expand

      fun mkTvar s 	 = Universes.mkUvar s
      val mkType 	 = Term.mkTyp
      fun mkTcon n 	 = mkType(Universes.mkUcon n)
      fun mkTypen nod 	 = mkType(Universes.tocNode nod)
      fun mkTypeGe j i 	 = mkType(Universes.mkUvarGe j i)
      fun mkTypeGt i 	 = mkType(Universes.mkUvarGt i)

      open Term  

      val dnf = UMopen.UMdnf
      val whnf = UMopen.UMwhnf
      val thryUMwhnf = UMopen.thryUMwhnf

      val sub = Subst.sub 
      val subst1 = Subst.subst1 

      val par_unif = ParTm.par_unif

(* 2011: moved from subst; replaced by abst!   *)
(* Substitute Rel(1) for Ref(br) *)
(* unsafe psub: M[p:=0] to witness shape_lemma *)

(*
fun subst2 bref = 
  let fun subrec k =
    fn (Ref br)  => if sameRef br bref then Mod(Rel k) else UMod
     | (App b)   => mkApp (subrec k) b
     | thry as Bind(b as ((Thry,_),_,_,_)) =>
	 ((* if (!theory_debug) 
	     then (prs"\n##thry_debug:subst2 in ";legoprint thry)
	  else ()*) 
	  thry_debug "\n##thry_debug:subst2 in " legoprint thry;
	  mkBind subrec k b)
     | (Bind b)  => mkBind subrec k b
     | (Tuple b) => mkTuple (subrec k) b
     | (CnLst b) => mkCnLst (subrec k) b
     | (Proj b)  => mkProj (subrec k) b
     | (RedTyp b)=> mkRedTyp (subrec k) b
     | (LabVT b) => mkLabVT (subrec k) b
     |  Var(n,t) => if depends bref t
		      then failwith("type of metavar "^Int.toString n^
				    " not closed")
		    else UMod
     | _         => UMod
  in share (subrec 1) end;
 *)

fun subst2 bref = 
    let
	val P = fn Ref br   => sameRef br bref 
	      	 | Var(n,t) => if depends bref t
		      	       	  then failwith("type of metavar "^
			       	    	      	 Int.toString n^
				    	      	" not closed")
		    	       else false
		 | _ => false
    in 
       Abst.abst P 
    end

in 

(* Machine performs some basic manipulations on (term:type) pairs *
 * subject to certain basic well-formedness checking, e.g. sorts  *
 * somewhat akin to Bert's system tpts/ots  	      	   	  *)

  (* moved from toc *)

  fun coerceGe c = c; (* who knows what this once meant? *)

  fun ConsiderTerm c = (c, Toc.type_of_constr c); (* encapsulates Toc.toc *)

local
  (* for side-effects in Namespace *)
  fun consider br (cxt:context) = (Ref(br),coerceGe(ref_typ br)) 
in
  fun ConsiderNam nam cxt = consider (Context.searchCxt nam cxt) cxt
end; 

  fun ConsiderVar n t  = (Var(n,t),coerceGe t)
  fun ConsiderProp()   = (Prop,mkTcon 0) (*Prop,mkTyp(uconst 0)*)
  fun ConsiderTheory() = (Theory,mkTcon 0) (*Theory,mkTyp(uconst 0)*)

  fun ConsiderType(s) =
    let
      fun typez i = 
	case Theories.theory()
	  of Theories.xtndCC => (mkType(i),mkTypeGt(i)) (* uvar "" [UniGt i] *)
	   | _      => bug"typez"
    in typez (mkTvar s)
    end

  fun ConsiderTypen(n) = (mkTcon n,mkTcon (succ n)) (*mkTyp(uconst n),mkTyp(uconst (succ n))*);

  fun arg_occur (Bind ((Pi,_),_,dom,ran)) br =
      depends br dom orelse arg_occur ran br
    | arg_occur _ _ = false

  fun letize (V,T) br =
    let val ((_,vis),s,c,_) = ref_bd br
    in (MkBind((Let,vis),s,c,subst2 br V),
	coerceGe(MkBind((Let,vis),s,c,subst2 br T)))
    end;

local
      fun mkImplicit vis c br = if vis = VBot
                       	      	 then if arg_occur c br then Hid else Vis
                  		else vis

      fun failLFdom() = (failwith"LF: only a Prop can be the domain of a function")
      fun failCCran() = (failwith"Pure CC: Type can not be the range of a function")

      fun msgDom act s ct = (prs("attempt to "^act^" "^s^" : "); prnt_vt_expand ct)
      fun msgRan act ct =   (prs("attempt to "^act^" over "); prnt_vt_expand ct)

      fun msgPrj vt = (prs"\nattempt to project\n  ";prnt_vt_expand vt)

in

  fun abstract (V,T) br = (* the Lda rule in PTS *)
    let
      val ((_,vis),s,c,t) = ref_bd br
      val vis = mkImplicit vis T br 
      fun abstr() = (MkBind((Lda,vis),s,c,subst2 br V),
		     MkBind((Pi,vis),s,c,subst2 br T))
      fun failCC U = (msgRan"abstract" (V,U);failCCran())
      fun failLF() = (msgDom"abstract" s (c,t);failLFdom())
    in case Theories.theory()
	 of Theories.pureCC => (case whnf T
			 of (U as (Type _)) => failCC U
			  |     _      	    => abstr())
	  | Theories.xtndCC => abstr()
	  | Theories.lf     => case t of Prop => abstr() | _ => failLF()
    end;

  fun generalize (VT as (V,T)) br = (* the Pi rule in PTS *)
    let
      val ((_,vis),s,c,t) = ref_bd br
      val vis = mkImplicit vis V br
      val _ = if !gen_debug 
      	      	 then (prs("\n** gen debug ** "^ref_nam br^", ");
		       prnt_vt VT)
	      else()
      val typ =
	case (t,whnf T)
	  of (_,Prop)		  => Prop
	   | (Prop,Ti as Type(i)) => Ti (*mkType(i)*)  (* new level var NOT needed here *)
	   | (Type(j),Type(i)) 	  => mkTypeGe j i (* uvar "" [UniGe(i),UniGe(j)] *)
	   | _ => (msgRan"generalize" VT; failSORT"the range of a product") 

      fun failLF() = (msgDom"generalize" s (c,t);failLFdom()) 

      fun genlz() = (MkBind((Pi,vis),s,c,subst2 br V),typ) 

    in case Theories.theory() of Theories.xtndCC => genlz()
       	    	      | Theories.pureCC => genlz()
  		      | Theories.lf     => case t of Prop => genlz() 
		      	       	       	      |  _	 => failLF()
    end;

  fun sigize (VT as (V,T)) br =
    let
      val ((_,vis),s,c,t) = ref_bd br
      val typ =
	case (t,whnf T)
	  of (Prop,Prop) => if (!Theories.AczelMode) then mkTcon 0
			    else Prop
	   | (Prop,Ti as Type(i)) => Ti
	   | (Ti as Type(i),Prop) => Ti
	   | (Type(j),Type(i)) => mkTypeGe j i (* uvar "" [UniGe(i),UniGe(j)] *)
	   | (t,T) => (message"Error typechecking SIGMA:";
		       prnt_vt (V,T); legoprint T;
		       failSORT"the domain and range of SIGMA")
      fun sigz() = (MkBind((Sig,vis),s,c,subst2 br V),typ)
      fun failure() = failwith"No SIGMA in current theory"
    in case Theories.theory()
	 of Theories.xtndCC => sigz()
	  | Theories.pureCC => failure()
	  | Theories.lf     => failure()
    end;

  fun Apply sbst mkVar pv (VTf as (Vf,Tf)) (VTa as (Va,Ta)) =
    let val Tf = whnf (sub sbst Tf)
    in case (pv,Tf,VTa)
	 of (ShowNorm,Bind((Pi,Hid),nam,dom,rng),_) =>
	   let val var = mkVar dom  (* 2011: var supposed to be a Var; make explicit? *)
	     val newVf = App((Vf,[var]),[NoShow])
	   in Apply sbst mkVar ShowNorm (newVf,coerceGe (subst1 var rng)) VTa
	   end
	  | (ShowForce,Bind((Pi,Hid),nam,dom,rng),_)  =>
	      Apply sbst mkVar ShowForce (Vf,Bind((Pi,Vis),nam,dom,rng)) VTa
	  | (NoShow,Bind((Pi,Hid),nam,dom,rng),_)  =>
	      Apply sbst mkVar NoShow (Vf,Bind((Pi,Vis),nam,dom,rng)) VTa
	  | (pv,Bind((Pi,Vis),_,dom,_),(Bot,Bot)) =>
	      Apply sbst mkVar pv VTf (mkVar dom,dom)
	  | (pv,Bind((Pi,Vis),nam,dom,rng),_) =>
	      let
		val _ = if (!mach_debug) 
		      	   then (message"** mach_deb; App";
			         legoprint Vf; legoprint Va)
			else () 

	      in case par_unif sbst Ta dom of
		SOME(s) => ((MkApp((Vf,[Va]),[pv]),coerceGe (subst1 Va rng)),s)
	      | NONE => raise Error.error(Error.mkAPPLNTYPE [Vf,dnf dom,Va,dnf Ta]) (* *** *)
	      end
	  | (_,Bind((Pi,_),_,_,_),_) => bug"Apply; unknown Pi"
	  | _  => raise Error.error(Error.mkAPPLNNFUN [Vf, dnf Tf]) (* *** *)
    end;

  (* (eager) Projections of Sigma *)
  fun Projection proj (V,T) =
    case whnf T of
      Bind((Sig,_),s,d,r) =>
	(case (V,proj)
	   of (Tuple(_,c::cs),Fst) => (c,d)
	    | (Tuple(_,c::cs),Snd) => let val r = subst1 c r
				      in  (MkTuple(r,cs),r)
				      end
	    | (_,Fst) => (MkProj(proj,V),d)
	    | (_,Snd) => (MkProj(proj,V),MkBind(LetDef,s,MkProj(Fst,V),r))
	    | _ => bug"Projection1")
    | whnfT => (msgPrj (V,dnf whnfT);
		failwith"Projection: type of body not a SIG");

(* *********************** adapted from toc.sml *********************** * 
(* projections from Theories? *)
fun ProjectLabel lab (V,Theory) = (* Th =/= Theory should throw failure *)
  case thryUMwhnf V of  (* theory must be in whnf to see its labels *)
    Bind((Thry,_),_,_,CnLst lvts) => 
      let 
	fun assoc (LabVT(Name l,_,A)::rest) = if l=lab then A else assoc rest
	  | assoc [] = failwith("label `"^lab^"' doesn't occur in Theory")
	  | assoc _  = bug"TheoryProject; assoc"
	val T = assoc lvts
      in (Proj(Labl lab,V),subst1 V T)
      end

     | _ => (message("Cannot theory project "^LegoUtils.dquote(lab)^" from ");
		     legoprint V;
		     failwith"Theory projection fails")

  | ProjectLabel lab (_,T) = (message("Cannot project: ");
    		      	      legoprint T; 
			      failwith("Not a theory!"))

 * ******************************************************************** *)
end;


    (**   tuples  **)
  local
    (* for our tuple representation we need a "Sigma normal form": all
     * rightmost Sigmas must be explicit *)
    fun errRpt t T lr = (message"constructing tuple:";
			 legoprint t; 
			 message"isn't a specialization of";
			 legoprint T;
			 failwith("tuple doesn't have purported type on "^lr))
    fun chkTpl (T:cnstr) (vts:(cnstr*cnstr)list) sbst = 
      case (whnf T,vts)
	of (Bind((Sig,_),_,tl,tr),(v,t)::(vts as _::_)) =>
	  (case par_unif sbst t tl
	     of SOME(sbst) => chkTpl (subst1 v tr) vts sbst
	      | NONE => errRpt t tl "left")
	 | (T,[(v,t)]) => (case par_unif sbst t T
			     of SOME(sbst) => sbst
			      | NONE =>  errRpt t T "right")
	 | _ => failwith"tuple doesn't have a Sigma type"
  in

(* 1998 version *
    fun tuplize sbst Bot (vts as _::_::_) =  (* infer the flat product... *)
      let 
      	val (_, ts) = ListPair.unzip vts
	val (endtype,prefix) = LegoUtils.removeLast ts 
	    		       handle Empty _ => bug"tuplize" (* shouldn't happen *)
      	fun mkT (t,T) = Bind((Sig,VBot),"",t,T)
	val T = List.foldr mkT endtype prefix (* 2011: List.foldr *)
	val _ = Toc.type_of_constr T     (* check T has a sort; !toc ? *)
      in  tuplize sbst T vts
      end
      | tuplize sbst T (vts as _::_::_) = (* ...or use the given Sigma type *)
	let 
      	    val (vs,_) = ListPair.unzip vts
	    val sbst = chkTpl T vts sbst
	in  ((MkTuple(T,vs),T),sbst)
	end
      | tuplize _ _ _ = bug"tuplizec"
 *)

(* 2011 version *)
    fun tuplize sbst T (vts as vt::(vt0n as (vt0::vt1n))) = 
      let 
      	val (vs,ts) = ListPair.unzip vts
	val sigT = 
	 (case T 
	    of Bot => (let (* infer the flat product... *)
			 val (t::t0::t1n) = ts (* vts shape tells us this must be so *)
(* SigVBot *)		 fun mkT (t,T) = Bind((Sig,VBot),"",t,T) 
			 fun sigmaTL s   []    = s
			   | sigmaTL s (t::ts) = mkT (s,(sigmaTL t ts))
			 val flatT = mkT(t,(sigmaTL t0 t1n)) 
			 val _ = Toc.type_of_constr flatT (* check T has a sort *)
		      in 
		      	 flatT
		      end handle Match => bug"tuplize" (* so this shouldn't happen *))
	     |  _  => T) (* ...or use the given Sigma type *)
	val sbst = chkTpl sigT vts sbst
      in  ((MkTuple(sigT,vs),sigT),sbst)
      end
      | tuplize _ _ _ = bug"tuplizec: not enough elements to make a Tuple" (* 0,1??? *)
  end;

(* moved from Namespace: extend Machine ops to contexts *)
fun dischCxt VT cxt =
  let
    fun preDischCxt br =
      case ref_bind br
	of Let => letize VT br
	 | Lda => abstract VT br
	 | Pi  => generalize VT br
	 | Sig => sigize VT br
	 | Thry => bug"dischCxt"
  in if Context.isEmptyCxt cxt 
     then failwith"cannot discharge; context empty"
     else let val (br,brs) = Context.popCxt cxt
     	  in (preDischCxt br,br,brs)
	  end
(* (* 2011: need to have explicit list destructors for Context *)
     case cxt 
       of br::brs  => (preDischCxt br,br,brs)
        |   []     => failwith"cannot discharge; context empty"
 *)
  end

fun lclGenCxt vt backto cxt = (* *** for Concrete.fEval *** *)
    let
	fun dch (vt as (v,t)) br =
	    if (depends br v) orelse (depends br t)
		then case ref_bind br of
		     	  Let => letize vt br
		  	| Lda => abstract vt br
		  	|  _  => bug"funny Gen"
	    else vt
	fun step vt cxt = if Context.isEmptyCxt cxt 
     	    	    	  then failwith(backto^" undefined or out of scope")
     			  else let 
			       	   val (br,rmndr) = Context.popCxt cxt
				   val nvt = dch vt br
     	  		       in 
			       	  if sameNam br backto then nvt
				  else step nvt rmndr
			       end 
(* 	  case cxt 
	    of br::rmndr => let val nvt = dch vt br
			    in  if sameNam br backto then nvt
				else step nvt rmndr
			    end
	     |   [] 	 => failwith(backto^" undefined or out of scope") 
 *)
    in 
	step vt cxt (* gets applied to a cxt then *)
    end

(* 2011: bad type sharing constraints caused this rearrangement *)

fun mkNewBnd knd (pfx as Prefix(b,vis,frz_flg,par_flg,deps)) nam (v,t) 
   = (* *** also want this for Concrete.fEval *** *)
    let
      fun Assume t k =
	let 
	    val K = whnf k (* kind k takes whnf... so... *)
	    val tK = (t,K)
	in if isKind K (* *** andalso Pure nam t *** *)
	     then Term.mkNewBnd knd (Prefix(b,vis,UnFroz,par_flg,deps)) nam tK
	   else (Pretty.print_cannot_assume nam tK; (* 2011: now (t,K)  *)
		 failSORT"assumed")
	end

      fun Define v t =
	let
	  val _ = Pure nam v
	  val T = dnf t
	in
	  Term.mkNewBnd knd pfx nam (v,T)
	end
    in
      case (b,vis)
	of (Let,Def) => Define v t
	 | (Let,_)   => bug"extendBnd:Let,_"
	 | (_,Def)   => bug"extendBnd:_,Def"
	 | bv        => Assume v t
    end

(* extendCxt ... up to but not including extendCxtGbl ... *)

fun addNewBnd knd pfx nam vt cxt = 
    Context.addBndCxt (mkNewBnd knd (pfx) nam vt) cxt

fun mkBndFresh knd (pfx) nam vt cxt =
    if Context.unDefined nam cxt 
      then (mkNewBnd knd pfx nam vt)
    else failwith(Utils.StringUtil.dquote(nam)^" already in namespace")

fun addBndFresh knd (pfx) nam vt cxt = 
    Context.addBndCxt (mkBndFresh knd (pfx) nam vt cxt) cxt 

(*
fun addBndFresh knd (pfx) nam vt cxt = 
    if Context.unDefined nam cxt 
      then (addNewBnd knd pfx nam vt cxt)
    else failwith(Utils.StringUtil.dquote(nam)^" already in namespace")

 *)


end (* local defns *)
end (* FunMachine *)
