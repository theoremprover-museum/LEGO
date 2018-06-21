(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* concrete.sml *)

functor FunConcrete (structure Term:TERM
		     structure Context:CONTEXT
		     structure Subst:SUBST
		     structure UMopen:UMOPEN 
		     structure Toc:TOC 
		     structure Unif:UNIF 
		     structure ParTm:PARTM
		     structure Pretty:PRETTY
		     structure Machine:MACHINE
		     sharing 
		   	   type Term.cnstr
			      = Context.cnstr
			      = Subst.cnstr
			      = UMopen.cnstr
			      = Toc.cnstr
			      = Unif.cnstr
			      = ParTm.cnstr
			      = Pretty.cnstr
			      = Machine.cnstr
		     and 
		   	   type Term.binding
			      = Context.binding
			      = Subst.binding
			      = Pretty.binding
			      = Machine.binding
		     and 
		   	   type Context.context
			      = Pretty.context
			      = Machine.context
		     and 
		   	   type Subst.assignment
			      = Unif.assignment
		     and 
		   	   type Subst.substitution
			      = Unif.substitution
			      = ParTm.substitution
			      = Machine.substitution
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

		     ) (* Namespace only at the end *)

(* *** *
structure Concrete
 * *** *)
	: CONCRETE 

  =

struct

  	type binding = Context.binding

	type cnstr = Context.cnstr
	type context = Context.context
	type substitution = Subst.substitution

	type Prefix = Term.Prefix
	type instrs = Term.instrs
	type Frz = Term.Frz
	type projSort = Term.projSort
	type bindSort = Term.bindSort
	type visSort = Term.visSort
	type prntVisSort = Term.prntVisSort
	type LocGlob = Term.LocGlob

(* *)

(* ******************************************************************** *)

   type 'b binder = Prefix * string list * 'b
   type 'b ctxt = 'b binder list 

(* ******************************************************************** *) 
(* for funny abstraction failures in ind_relations *)

   fun unBind bd = bd  
   fun unCtxt cxt = cxt 

   fun mkBind bd = bd  
   fun mkCtxt cxt = cxt 

(* ******************************************************************** *)
(* ******************************************************************** *)

local 

      val message = Printing.message

      val legoprint = Pretty.legoprint
      val prnt_vt_expand = Pretty.prnt_vt_expand
      
      val sub = Subst.sub
      val sub_pr = Subst.sub_pr
      val nilS = Subst.nilS 

      val par_tm = ParTm.par_tm
      val par_unif = ParTm.par_unif

      open Utils.Except
      open Utils.ListUtil 
      open Utils.StringUtil 
      open Term 

in 

val eval_debug = ref false;
val hold_T = ref Bot;
val hold_cnj = ref Bot;

(* La syntaxe concrete *)
datatype cnstr_c = Bot_c
| Prop_c
| Theory_c
| Type_c of string
| TypeAbs_c of int
| Ref_c  of string
| App_c  of prntVisSort * cnstr_c * cnstr_c
| Bind_c of (cnstr_c binder) * cnstr_c
| Tuple_c of (cnstr_c list) * cnstr_c
| Proj_c of projSort * cnstr_c
| Ctxt_c of (cnstr_c ctxt) * cnstr_c
| Cast_c of cnstr_c * cnstr_c       (* strong cast *)
| wCast_c of cnstr_c * cnstr        (* weak cast *)
| Case_c of cnstr_c * ((cnstr_c ctxt) * cnstr_c * cnstr_c) list  (* case *)
| Red_c of (cnstr_c ctxt) * ((cnstr_c*cnstr_c) list)
| Var_c  of int  (* metavars for use in refinements *)
| NewVar_c       (* make a new metavar *)
| Normal_c of cnstr_c
| Hnf_c of int * cnstr_c
| Dnf_c of cnstr_c
| RedTyp_c of instrs * cnstr_c
| TypeOf_c of cnstr_c
| Gen_c of cnstr_c * string

(*
withtype binder_c = cnstr_c binder  
 	   (* bindVisSort * frzLocGlob * string list * string list * cnstr_c *)
and 	 ctxt_c = cnstr_c ctxt (* binder_c list *);
 *)

   type binder_c = cnstr_c binder
   type ctxt_c = cnstr_c ctxt

   val nil_c = [] 
   fun cons_c b c = b :: c

val red_cache = ref ((nil_c:ctxt_c),(nil_c:(cnstr_c*cnstr_c) list));

fun prt_concrete c =
  let val prbd =
    fn Lda => "Lda" | Pi => "Pi" | Sig => "Sig"
     | Let => "Let" | Thry => "Thry"
  in  case c of Bot_c => "Bot"
  | Prop_c   	      => "Prop"
  | Theory_c 	      => "Theory"
  | Type_c(_) 	      => "Type"
  | TypeAbs_c(n)      => "(Type"^Int.toString n^")"
  | Ref_c(s)  	      => "(Ref "^s^")"
  | App_c(_,f,a)      => "("^prt_concrete f^" "^prt_concrete a^")"
  | Bind_c((Prefix(b,v,_,_,_),ns,c),d) => "("^prbd b^")" (* 1998/2011: ??? *)
  | Tuple_c(cs,c) 	    => "(Tup "^concat_comma (List.map prt_concrete cs)^")"
  | Proj_c(Fst,c) 	    => "("^prt_concrete c^".1)"
  | Proj_c(Snd,c) 	    => "("^prt_concrete c^".2)"
  | Proj_c(Labl(l),c) 	    => "("^prt_concrete c^"^"^l^")"
  | Ctxt_c(_) 	 => "Ctxt"
  | Cast_c(c,d)  => "(Cast "^prt_concrete c^prt_concrete d^")"
  | wCast_c(c,v) => "(Cast "^prt_concrete c^",_)"
  | Case_c (_) 	 => "Case" (* case: cnstr_c * (ctxt_c * cnstr_c * cnstr_c) list  *)
  | Red_c(_) 	 => "Red"
  | Var_c(n)  	 => "(Var"^Int.toString n^")"
  | NewVar_c 	 => "NewVar"
  | Normal_c(_)  => "Norm"
  | Hnf_c(_) 	 => "Hnf"
  | Dnf_c(_) 	 => "Dnf"
  | RedTyp_c(_)  => "RedTyp"
  | TypeOf_c(_)  => "TypeOf"
  | Gen_c(_) 	 => "Gen"
  end

(* ******************************************************************** *)

val TYPE_c = Type_c ""

(* indicators, for tactics, newtop, conor-top, relation, ... *)

fun isBot Bot_c       = true
  | isBot _           = false

fun isRef (Ref_c(x))       = true
  | isRef _                = false

fun isHead (App_c(_,c1,c2)) = isHead c1
  | isHead      c           = isRef c

fun isTYPE (Type_c("")) = true
  | isTYPE _            = false

(* destructors, for newtop, conor-top, relation, ... *)

exception getConcrete

fun getRefNam v_c = case v_c
                      of (Ref_c nam) => nam
                       |       _     => raise getConcrete 

fun getAppData v_c = case v_c
                       of (App_c appdata) => appdata 
                        |       _         => raise getConcrete 

fun getBinder v_c = case v_c
                      of (Bind_c bd) => bd
                       |       _     => raise getConcrete 

fun getEndType (Bind_c(_,s))         = getEndType s
 |  getEndType (v_c as Ref_c(s))     = v_c
 |  getEndType (v_c as Type_c(s))    = v_c
 |  getEndType (v_c as Prop_c)       = v_c
 |  getEndType (v_c as TypeAbs_c(n)) = v_c
 |  getEndType   _                   = raise getConcrete

fun getEnd (Bind_c(_,s))  = getEnd s
 |  getEnd (App_c(_,s,_)) = getEnd s
 |  getEnd (Ref_c(s))     = s
 |  getEnd   _            = raise getConcrete

fun subForType st (Bind_c(x,s)) = let val t = subForType st s  
    	       	  		   in Bind_c(x,t)
				  end 
 |  subForType st (Type_c(""))  = Type_c(st)
 |  subForType st _ 		= raise getConcrete

exception errConcrete (* potentially raised by each of these *)

(* A function to test whether or not a term contains
   a variable name, first argument is the list of
   those names *)

fun contains l (Prop_c)         = false 
  | contains l (Type_c(_))      = false 
  | contains l (TypeAbs_c(_))   = false 
  | contains l (Ref_c(x))       = member x l
  | contains l (App_c(_,c1,c2)) = (contains l c1) orelse (contains l c2) 
  | contains l (Bind_c((_,l1,c1),c2)) =
     (contains (filter_neg (fn x => member x l1) l) c1) 
                                  orelse (contains l c2)  
  | contains l (Tuple_c (l1,c)) = (contains l c) orelse 
       List.foldr (fn (x,y) => contains l x orelse y) false l1 
  | contains l (Proj_c(p,c))    = contains l c 
  | contains l (Cast_c(c1,c2))  = (contains l c1) orelse (contains l c2) 
  | contains l (Var_c(_))       = raise getConcrete
  | contains l (NewVar_c)       = raise getConcrete
  | contains l (Bot_c)          = false 
  | contains l _                = raise errConcrete; 

(* Substitution of b for a in concrete term c is
   subst (a,b) c *)

fun subForRef (a,b) (v_c as Ref_c(x)) = if a=x then b else v_c
  | subForRef p (v_c as Prop_c)       = v_c 
  | subForRef p (v_c as Type_c(s))    = v_c
  | subForRef p (v_c as TypeAbs_c(x)) = v_c
  | subForRef p (App_c(x,c1,c2))      = App_c(x,(subForRef p c1),(subForRef p c2)) 
  | subForRef (p as (a,b)) (v_c as Bind_c((pfx,l1,c1),c2)) =
      if (member a l1) 
         then v_c 
      else Bind_c((pfx,l1,(subForRef p c1)),(subForRef p c2)) 
  | subForRef p (Tuple_c(l1,c)) = Tuple_c(List.map (subForRef p) l1,subForRef p c)  
  | subForRef p (Proj_c(l,c))   = Proj_c(l,subForRef p c) 
  | subForRef p (Cast_c(c1,c2)) = Cast_c((subForRef p c1),(subForRef p c2)) 
  | subForRef p (Var_c(_))      = raise getConcrete
  | subForRef p (NewVar_c)      = raise getConcrete
  | subForRef p (v_c as Bot_c)  = v_c 
  | subForRef p _               = raise errConcrete; 

fun subForNam (a,b) = subForRef (a,Ref_c b) 

(* constructors, for lego.grm.sml etc.; nearly the whole interface? *)

val mkRef_c = Ref_c 

fun mkApp_c (f, e) = App_c(ShowNorm, f, e)
fun mkAppForce_c (f, e) = App_c(ShowForce, f, e)
fun mkAppNoShow_c (f, e) = App_c(NoShow, f, e)
fun mkLift_c V_c = mkApp_c (V_c, NewVar_c)
fun mkLiftForce_c V_c = mkAppForce_c (V_c, NewVar_c)

(* type/body changed 2011 *)

fun mkInfixApp_c (nam, e1, e2) = mkApp_c(mkApp_c(mkRef_c (Infix.infix_name nam),e1),e2) 

(* ****************************************************************** *

 * *** from lego-grm: decoding top-level decl/defn bindings ***

  DECL : LSQBR DLSLBIND RSQBR        ( let val ((x,y,z),w) = DLSLBIND 
                                        in (Lda,x,UnfLoc,w,y,z) end )
       | DOLLARSQ DLSLBIND RSQBR     ( let val ((x,y,z),w) = DLSLBIND
                                        in (Lda,x,UnfGlb,w,y,z) end )
       | LCBR DLSLBIND RCBR          ( let val ((x,y,z),w) = DLSLBIND
                                        in (Pi,x,UnfLoc,w,y,z) end )
       | LPTBR DLSLBIND RPTBR        ( let val ((x,y,z),w) = DLSLBIND
                                        in (Sig,x,UnfLoc,w,y,z) end )
        
  DEFN : LSQBR DNSLBIND RSQBR        ( let val ((x,y,z),w) = DNSLBIND 
                                        in (Let,x,UnfGlb,w,y,z) end )
       | DOLLARSQ DNSLBIND RSQBR     ( let val ((x,y,z),w) = DNSLBIND 
                                        in (Let,x,UnfLoc,w,y,z) end )
       | STARSQ DNSLBIND RSQBR       ( let val ((x,y,z),w) = DNSLBIND 
                                        in (Let,x,FrzGlb,w,y,z) end )

 * ****************************************************************** *)

val mkVis = Vis
val mkHid = Hid
val mkQM  = VBot

fun MkDecl b lg ((vis,y,z),x) 
  = (Prefix(b,vis,UnFroz,lg,x),y,z) : binder_c 

val mkLLda = MkDecl Lda Local
val mkGLda = MkDecl Lda Global
val mkLPi  = MkDecl Pi  Local
val mkLSig = MkDecl Sig Local


fun MkDefn (frz_flg,par_flg) ((y,z),x) 
  = (Prefix(Let,Def,frz_flg,par_flg,x),y,z) : binder_c 

val mkLDefn = MkDefn UnfLoc
val mkGDefn = MkDefn UnfGlb
val mkFDefn = MkDefn FrzGlb

val mkBind_c = Bind_c

fun mkBindExp_c b v lg nams dom body 
  = mkBind_c ((Prefix(b,v,UnFroz,lg,[]),nams,dom),body)

(* 
fun mkLBindExp_c b v nams dom body 
  = mkBind_c ((Prefix(b,v,UnFroz,Local,[]),nams,dom),body)

fun mkGBindExp_c b v nams dom body 
  = mkBind_c ((Prefix(b,v,UnFroz,Global,[]),nams,dom),body)
 *)

fun mkLBindExp_c b v = mkBindExp_c b v Local

fun mkGBindExp_c b v = mkBindExp_c b v Global

fun mkBind0_c b (dom,body) = mkLBindExp_c b mkVis [""] dom body 

val mkPiExp_c = mkBindExp_c Pi 
val mkLdaExp_c = mkBindExp_c Lda 

val mkArr_c = mkBind0_c Pi   (* *** use Bot_LG instead of Local? *** *)

val mkLda_c = mkBind0_c Lda

val mkSig_c = mkBind0_c Sig

fun mkFst_c c = Proj_c(Fst, c)
fun mkSnd_c c = Proj_c(Snd, c)

val mkTuple_c = Tuple_c
fun mkLabProj_c (id,c) = Proj_c(Labl(id), c)

val mkRed_c = Red_c

fun mkRed0_c reds = Red_c(nil_c,reds)

fun mkRedTyp_c c = RedTyp_c(iNrml,c)

local
	fun failure typstr = typstr^" not in the language of "^Theories.ThytoString()
	val strType = Utils.StringUtil.squote "Type"
	val strTypeAbs = Utils.StringUtil.squote "Type(.)"
in
   fun mkType_c () = let 
       		     	 val T = Theories.theory()
			 val msg = failure strType
       		     in case T
               	       of   Theories.lf	   => Prop_c
                       	  | Theories.pureCC => failwith msg 
                	  | _  	   => TYPE_c 
       		     end

   exception TypeNamError of cnstr_c

   fun mkTypeNam_c c = let 
       		       	   val T = Theories.theory()
       		       	   val msg = failure strTypeAbs
       		       in  case T
               	       	   of   Theories.lf     => failwith msg
                       	      | Theories.pureCC => failwith msg
                	      | _      => (case c of Ref_c id => Type_c id
			      	     	      | _ => raise TypeNamError c ) 
       		       end


   fun mkTypeAbs_c n = let 
       		       	   val T = Theories.theory()
       		       	   val msg = failure strTypeAbs
       		       in case T
               	       	  of   Theories.lf     => failwith msg
                       	     | Theories.pureCC => failwith msg
                	     | _      => TypeAbs_c n 
       		       end
			
end

(* *)


(* Make concrete from abstract: use the fresh name generator *)
local

    val okLoc = isNullString

    fun okGlb Cxt nam = Context.unDefined nam Cxt

in

 fun unEval_ Cxt = (* extra Cxt local to push_nam/fresh_nam *)
  let 

    val fresh_nam = fresh okLoc (okGlb Cxt) (* *** see!!! *** *)

(* **************************************************************** *
      if n="" orelse (unDefined n Cxt andalso not (member n nams))
      	      	     (* *** formerly Namespace.isNewName n *** *)
	then (n,n::nams)
      else push_nam (n^"'"^(Int.toString (succ(length nams)))) nams
 * **************************************************************** *)

    fun uerec nams =
      fn Prop            => Prop_c
       | Theory          => Theory_c
       | Type(n)         => Universes.nodeCase TYPE_c Type_c TypeAbs_c n
       	 		    (*case n
			       of Uconst(m) => TypeAbs_c(m)
				| Uvar(Unnamed _,_) => Type_c ""
				| Uvar(Named s,_) => Type_c s *)
       | Ref(br)         => mkRef_c(ref_nam br)
       | Rel(n)          => mkRef_c(nth nams n handle Nth _ => bug"uerec")
       | App((f,args),viss) => 
	   let fun app ((arg,vis),f) = App_c(vis,f,uerec nams arg) (* 2011: List.foldl *)
	   in  List.foldl app (uerec nams f) (ListPair.zipEq (args,viss)) (* zipEq *)
	   end 	     	 	     				 (* 2011: List.foldl *)
       | LabVT(l,v,t) =>
	   (case l of
	      Name _ => bug"unEval:LabVT Name"
	    | WeakCast => wCast_c(uerec nams v,t)
	    | StrongCast => Cast_c(uerec nams v,uerec nams t)
	    | RedPr => bug"unEval:LabVT RedPr")
       | CnLst _ => bug"uerec:CnLst"
       | Case _ => bug"uerec:Case"
       | Bind((Thry,v),n,c,d) => bug"uerec:Thry"
       | Bind((b,v),n,c,d) =>
	   let val new = fresh_nam n nams 
	   in  Bind_c((Prefix(b,v,UnFroz,Local,[]),[new],uerec nams c),uerec (new::nams) d)
	   end
       | Tuple(T,ls)     => Tuple_c(List.map (uerec nams) ls,uerec nams T)
       | Proj(p,c)       => Proj_c(p,uerec nams c)
       | RedTyp(p,c)     => RedTyp_c(p,uerec nams c)
       | Var(n,c)        => Cast_c(Var_c n,uerec nams c)
       | Bot             => bug"uerec:Bot"
  in
    (uerec [])
  end

end; (* of local, for fresh *)

local 

    val dnf  = UMopen.UMdnf
    val whnf = UMopen.UMwhnf
    val norm = UMopen.UMnorm 
    val type_match = UMopen.UMtype_match

    fun redn i = case i of iNrml => norm (* *** temporary *** *) 

in 

fun fEval_ Cxt type_of_var mkVar V_c =
  let
    fun Eval cxt sbst c =
      let val (VT,sbst) = eval cxt sbst c
      in (sub_pr sbst VT,sbst) end (* 2011: moved from Unif !!! *)

    and Cval c cxt sbst = Eval cxt sbst c

    and eval cxt sbst c =
      let
	val _ = if (!eval_debug) then message("** eval_deb: "^prt_concrete c)
		else ()
	fun Eval_arg cxt sbst =
	  fn NewVar_c => ((Bot,Bot),sbst)   (* just a marker for Apply *)
	   | x        => Eval cxt sbst x
      in case c of
	Prop_c => (Machine.ConsiderProp(),sbst)
      | Theory_c => (Machine.ConsiderTheory(),sbst)
      | Type_c s => (Machine.ConsiderType s,sbst)
      | TypeAbs_c(n) =>
	     if (n>=0) then (Machine.ConsiderTypen n,sbst)
	     else failwith((Int.toString n)^" not a valid Type level")
      | Ref_c(nam) => (Machine.ConsiderNam nam cxt,sbst) 
      | Bind_c(bnd,r) => EvLoc bnd (Cval r) cxt sbst
      | App_c(pv,fnn,arg) =>
	  let val (VTfun,sbst) = Eval cxt sbst fnn
	      val (VTarg,sbst) = Eval_arg cxt sbst arg
	  in  Machine.Apply sbst mkVar pv VTfun VTarg 
	  end
      | Tuple_c(cs,t) => (* 2011: List.foldl *)
	  let val ((T,_),sbst) = case t of Bot_c => ((Bot,Bot),sbst)
				         |   _   =>  Eval cxt sbst t
	      fun ev (c,(vts,sbst)) = let val (vt,sbst) = Eval cxt sbst c
				      in  (vt::vts,sbst)
				      end
	      val (vts,sbst) = List.foldr ev ([],sbst) cs (* 2011: List.foldl *)
	  in  Machine.tuplize sbst T vts
	  end
      | Proj_c(p,c) =>
	  (case (Eval cxt sbst c,p)
	     of (((V,_),sbst),Labl l) => ((Toc.TheoryProject l V),sbst)
	      | ((VT,sbst),_) => ((Machine.Projection p VT),sbst))
      | Case_c(v,branches) =>
	  (case Eval cxt sbst v of
	     ((V,T),sbst) => ((Case(V,EvCase T branches cxt),T),sbst))
      | RedTyp_c(i,c)  => (case Eval cxt sbst c of   (****  temporary  *****)
			     ((v,t),sbst) => ((RedTyp(i,v),redn i t),sbst))
      | Cast_c(c,t)    => typecheck cxt sbst c t
      | wCast_c(c,t)   => typchk cxt sbst c t
      | Ctxt_c(locs,c) => EvLocs locs (Cval c) cxt sbst
      | Red_c(red)     => EvRed red cxt
      | Var_c(n)       => ((Machine.ConsiderVar n (type_of_var n)),sbst)
      | NewVar_c       => failwith"new scheme vars not allowed here" (* no_new_vars *)
      | Bot_c          => bug"fEval_:Bot_c"
      | Normal_c(c)    => (case Eval cxt sbst c of
			     ((v,t),sbst) => ((norm v,norm t),sbst))
      | Hnf_c(n,c)     => (case Eval cxt sbst c of
			     ((v,t),sbst) => ((whnf v,whnf t),sbst))
      | Dnf_c(c)       => (case Eval cxt sbst c of
			     ((v,t),sbst) => ((dnf v,dnf t),sbst))
      | TypeOf_c(c)    => (case Eval cxt sbst c of
			     ((v,t),sbst) => ((t,Toc.type_of_constr t),sbst))
      | Gen_c(c,back)  => (case Eval cxt sbst c of
			     (vt,sbst) => (Machine.lclGenCxt vt back Cxt,sbst))
			  (* *** formerly Namespace.lclGenCxtGbl vt back *** *)
			   (* *** too much generalisation? C/cxt >= NSP *** *)
      end
	 
    and typecheck cxt sbst pr cnj =  (* concrete conjecture *)
      let val ((Vcnj,_),sbst) = fEv cnj cxt sbst
      in  typchk cxt sbst pr Vcnj
      end

    and typchk cxt sbst pr cnj =     (* abstract conjecture *)
      case pr
	of NewVar_c => ((mkVar cnj,cnj),sbst) 
	 | _        =>
	     let
	       val ((V,T),sbst) = fEv pr cxt sbst
	       val _ = if (!eval_debug) 
	       	       	  then (message"**ev_deb: typchk ";
			        hold_T:= T; legoprint T;
			     	hold_cnj:= cnj; legoprint cnj)
		       else ()
	     in case par_unif sbst T cnj
		  of SOME(s) => ((V,cnj),s)
		   | NONE => (message"typechecking error.."; legoprint V;
			      message"has type.."; legoprint T;
			      message"which doesn't convert with..";
			      legoprint cnj;
			      failwith "term doesn't have purported type")
(* ******************  time slice? 
	     in case par_tm (sub sbst T) (sub sbst cnj) (* Unif *)
		  of true => ((V,cnj),sbst)
		   | false => (message"typechecking error.."; legoprint V;
			       message"has type.."; legoprint T;
			       message"which doesn't convert with..";
			       legoprint cnj;
			       failwith "term doesn't have purported type")
 * ********************** *)
	     end

    and chk_unresolved (VT as (V,T)) =
      if (semi_pure V) andalso (semi_pure T)
	then VT
      else (prnt_vt_expand VT; failwith "unresolved metavars")

    and fEv V_c cxt sbst = let val (VT,sbst) = Eval cxt sbst V_c
			   in ((chk_unresolved VT),sbst) end

    (* 2011: refactor Namespace addBndGbl and its use in newtop *)
    and binder ((pfx,nam,d)) inner_op cxt sbst =
      let 
	val (VT,sbst) = Eval cxt sbst d 
	val cxt = Machine.addNewBnd Bnd (pfxNullDeps pfx) nam VT cxt
          (* *** formerly Namespace.extendCxt Bnd (bv) frz_par_flg [] nam VT cxt *** *)
	val (VTr,sbst) = inner_op cxt sbst
	val (VT,_,_) = Machine.dischCxt VTr cxt
                (* *** Namespace.dischCxt VTr cxt *** *)
      in  (VT,sbst)
      end

    and EvLoc loc inner_op cxt sbst =
      case loc
	of (pfx,n::ns,d)
	  => binder (pfx,n,d)
	    (EvLoc (pfx,ns,d) inner_op)
	    cxt sbst
	| (_,[],_)    => inner_op cxt sbst 

    and EvLocs locs inner_op cxt sbst =
      case locs
	of bnd::bnds => EvLoc bnd (EvLocs bnds inner_op) cxt sbst
	 |    []     => inner_op cxt sbst

    and chkPr len (cxt:context) sbst (lhs,rhs) =
      let
	val lclCxt = (* List.take(cxt, (length locs)) (* 1998 *) *)
	    	     Context.takeCxt (len) cxt (* 2011 *)
	    	     handle _ => failwith "chkPr: too much local context" 
	val ((vlhs,tlhs),_) = Eval cxt sbst lhs
	val ((vrhs,trhs),_) = Eval cxt sbst rhs
	val _ = if (type_match tlhs trhs) then ()
		else (message"reduction LHS has type ";legoprint tlhs;
		      message"reduction RHS has type ";legoprint trhs;
		      failwith"LHS and RHS types don't convert")
	fun chkVarLR (br,b as (SOME _)) = b (* 2011: List.foldl *)
	  | chkVarLR (br,NONE) =
	    if depends br vrhs andalso not (depends br vlhs)
	      then SOME(ref_nam br) else NONE
	val _ = case List.foldl chkVarLR NONE lclCxt (* 2011: List.foldl *)
		  of NONE => ()
		   | SOME(s) =>
		       (message("reduction RHS mentions variable "^s);
			legoprint vrhs;
			message"reduction LHS does not ";legoprint vlhs;
			failwith"unbound variable in RHS")
      in LabVT(RedPr,vlhs,vrhs)
      end

    and EvRed (locs,pairs) cxt =
      let
	val _ = if !eval_debug then red_cache:= (locs,pairs) else ()
	val len = length locs
	fun er cxt sbst =    (** `CnLst' is a trick for discharge **)
	  ((CnLst(List.map (chkPr len cxt sbst) pairs),Bot),nilS)
      in
	EvLocs (locs) er cxt nilS 
      end

    and EvCase T branches cxt =
      let
	fun mk1Branch (locs,lhs,rhs) =
	  let
	    val len = length locs

	    fun chkBranch cxt sbst =
	      ((chkPr len cxt sbst (lhs,rhs),T),nilS)

	  in
	    EvLocs (locs) chkBranch cxt nilS 
	  end
	fun mk2Branch ((v,t),_) =
	  if type_match t T then v
	  else (message"Case body has type "; legoprint T;
		message"Case branch has type "; legoprint t;
		failwith"body and branch types don't convert")
	val branches = List.map (mk2Branch o mk1Branch) branches
      in CnLst(branches)
      end

  in

    fEv V_c Cxt nilS

  end;

end; (* local decl of whnf etc. *)

end; (* local decl of legoprint etc. *)

end; (* struct *)

(* ************************************************************ *
   NOTICE that we have refactored Namespace/Machine so that the
   following are the only appeals to Namespace, so they can be 
   moved elsewhere, using only fEval_ and unEval_ from here
 * ************************************************************ *)

functor FunConstructiveEngine
	(structure Term:TERM
	 structure Concrete:CONCRETE
	 structure Namespace:NAMESPACE
	 sharing 
	 	 type Term.cnstr
		    = Concrete.cnstr
		    = Namespace.cnstr
	 and	 type Concrete.context
		    = Namespace.context
	 and	 type Concrete.substitution
		    = Namespace.substitution
	 )
(* *** *
structure ConstructiveEngine
 * *** *)
	: CONSTRUCTIVEENGINE

 = 

struct 

       type cnstr = Term.cnstr 
       type cnstr_c = Concrete.cnstr_c 

       type context = Concrete.context 

       type substitution = Concrete.substitution 

local 

      val failwith = Utils.Except.failwith

      val mkVar = Term.Var 

      val fEval_ = Concrete.fEval_ 
      val unEval_ = Concrete.unEval_ 

      val type_of_Var = Namespace.type_of_Var 
      val getNamespace = Namespace.getNamespace 

in       

val mkRef_c = Concrete.mkRef_c 

(* a generator for metavars which can't occur in nature *)
fun parser_var_pack() = 
      let val NUN = ref(0)
      in  fn c => (NUN:= !NUN-1; mkVar(!NUN,c)) 
      end;

fun no_metavars n = 
  (failwith ("found metavar "^
	     (Int.toString n) ^"; metavars not allowed here")):cnstr

fun no_new_vars _ = failwith"`?' not allowed in here"; (* used nowhere? *)

(* only used in Discharge/Cut and in fEval *)
fun fEvalCxt cxt V_c = #1 (fEval_ cxt no_metavars (parser_var_pack()) V_c);

(* ************************************************************ *
   NOTICE that the following definitions need to be functional,
   because Namespace operations have side effects.  
 * ************************************************************ *)

fun unEval V = unEval_ (getNamespace()) V

fun fEval V_c = fEvalCxt (getNamespace()) V_c

    fun fEvalVal V_c = #1 (fEval V_c)
    fun fEvalTyp V_c = #2 (fEval V_c)


fun fEvalNam nam = fEval (mkRef_c nam)

    fun RefVal_s nam = fEvalVal (mkRef_c nam)
    fun RefTyp_s nam = fEvalTyp (mkRef_c nam)

fun EvalRefine_ type_of_var = fEval_ (getNamespace()) type_of_var 

fun EvalRefine mkvar = EvalRefine_ type_of_Var mkvar 

fun EvalRefine0 v_c = 
   let 
      val (VT,_) = EvalRefine (parser_var_pack()) v_c 
   in 
      VT
   end 

(* ***************************************************************** *)

end; (* local *)

end; (* struct *)