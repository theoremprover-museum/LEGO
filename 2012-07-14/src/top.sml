(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(*
   $Log: newtop.sml,v $
   Revision 1.5  1998/11/10 15:31:08  ctm
   Inductive definitions Label themselves

   Revision 1.4  1997/11/24 11:01:43  tms
   merged immed-may-fail with main branch

   Revision 1.3.2.3  1997/10/13 16:47:15  djs
   More problems with the above.

   Revision 1.3.2.2  1997/10/13 16:21:35  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.3.2.1  1997/10/10 17:02:43  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.3  1997/06/20 14:51:36  djs
   More changes to facilitate script management. Mostly to do with the
   protocol for annotations, but also changed the behaviour of lego wrt
   multiple declarations - now, if one fails, the others are rolled back.
  
   Revision 1.2  1997/05/08 13:56:05  tms
   Generalised Expansion Mechanism to Cope with Path information
*)

functor FunTop(
	structure Term:TERM
	structure Subst:SUBST
	structure UMopen:UMOPEN
	structure ParTm:PARTM
	structure Toplevel:TOPLEVEL
	structure Concrete:CONCRETE
	structure Namespace:NAMESPACE
	structure Engine:CONSTRUCTIVEENGINE
	structure Inductive:INDUCTIVE
	structure ConorInductive:CONORINDUCTIVE
        structure Expand:EXPAND 
        structure Pretty:PRETTY  
        sharing 
      		type Term.cnstr 
		   = Subst.cnstr 
		   = Expand.cnstr 
		   = UMopen.cnstr 
		   = ParTm.cnstr 
		   = Namespace.cnstr 
		   = Concrete.cnstr 
		   = Engine.cnstr 
		   = Pretty.cnstr 
	and 
		type Term.binding
		   = Subst.binding
		   = Namespace.binding
		   = Pretty.binding
     	and 
		type Subst.substitution
		   = ParTm.substitution
		   = Namespace.substitution
		   = Engine.substitution
     	and 
		type Concrete.cnstr_c
		   = Engine.cnstr_c
		   = Inductive.cnstr_c 
		   = Toplevel.cnstr_c

     	and 
		type Concrete.ctxt_c
		   = Inductive.ctxt_c 

		      and 
			      type Term.Prefix
			      	 = Namespace.Prefix
			      	 = Concrete.Prefix
			      	 = Inductive.Prefix
		      and 
			      type Term.Kind
			      	 = Namespace.Kind
		      and 
			      type Term.Frz
			      	 = Namespace.Frz
			      	 = Concrete.Frz
		      and 
			      type Term.LocGlob
			      	 = Namespace.LocGlob
			      	 = Concrete.LocGlob
			      	 = Inductive.LocGlob
		      and 
			      type Term.bindSort
			      	 = Concrete.bindSort
		      and 
			      type Term.visSort
			      	 = Concrete.visSort
			      	 = Inductive.visSort
			      	 = Pretty.visSort
		      and 
			      type Term.prntVisSort
			      	 = Concrete.prntVisSort
			      	 = Inductive.prntVisSort
		      and 
			      type Term.projSort
			      	 = Concrete.projSort
			      	 = Inductive.projSort
		)
(* *** * 
structure Top 
 * *** *)
	 : TOP 

 = 

struct

	type cnstr_c = Concrete.cnstr_c
	
(* ******************************************** *)

	    type 'b binder = Concrete.Prefix * string list * 'b 
	    type 'b ctxt   = 'b binder list

	    type binder_c = Concrete.binder_c
	    type ctxt_c = Concrete.ctxt_c

	    val unBind = Concrete.unBind : binder_c -> cnstr_c binder
	    val mkBind = Concrete.mkBind : cnstr_c binder -> binder_c

	    val mkCtxt = Concrete.mkCtxt o (List.map mkBind)
	    val unCtxt = (List.map unBind) o Concrete.unCtxt

(* ******************************************** *)

    val Pr = Toplevel.prAnnotating (* for the 1.3.1.1 patch for ProofGeneral? *)

(* scratch registers *)
local
	val message   = Printing.message 

	val legoprint   = Pretty.legoprint 
	val print_value = Pretty.print_value 
	val print_type  = Pretty.print_type 

        val dnf  = UMopen.UMdnf
        val whnf = UMopen.UMwhnf
        val norm = UMopen.UMnorm 

	val par_tm = ParTm.par_tm 

	val expand = Expand.Expand
	val expandAll = Expand.ExpandAll

	open Term  

	val VAL = ref Bot (* Prop *)
	val TYP = ref Bot (*(Type((Universes.uconst 0)));*)

  fun REGnf (REG:cnstr ref) nf = (REG:=(nf (!REG)); legoprint (!REG));

  fun REGExpand REG path nams =
    (REG := dnf (expand path nams (!REG)); legoprint (!REG));

  fun REGExpAll REG path n =
    (REG := (*dnf*) (expandAll path n (!REG)); legoprint (!REG));

  fun REGEquiv (REG:cnstr ref) (new:cnstr_c) =
    let 
    	val V = Engine.fEvalVal new
	val b = par_tm V (!REG)
	val _ = message (Bool.toString b)
    in  if b then REG:= V (* REG:= V; message"true" *)
	else () (* message"false" *)
    end

in

(* 2011: vanilla use of Type prevents sharing; Type0/mkTyp/mkUcon instead *)

  fun init_newtop() = (VAL:= Prop; TYP:= Type0); 

(** Reductions on subgoal, !VAL, !TYP **)

  fun V_Dnf _ = REGnf VAL dnf
  fun T_Dnf _ = REGnf TYP dnf

  fun V_Hnf _ = REGnf VAL whnf
  fun T_Hnf _ = REGnf TYP whnf

  fun V_Normal _ = REGnf VAL norm
  fun T_Normal _ = REGnf TYP norm

  val V_Equiv = REGEquiv VAL
  val T_Equiv = REGEquiv TYP

  fun V_Expand path nams = REGExpand VAL path nams
  fun T_Expand path nams = REGExpand TYP path nams

  fun V_ExpAll path n = REGExpAll VAL path n
  fun T_ExpAll path n = REGExpAll TYP path n

  fun StoreVT (V,T) =
  let
    val nam = (case V
		 of (Ref br) => if ref_isDefnNow br
				  then (ref_nam br)
				else ""
		  |    _     => "")

    val _ = VAL:= (case V of (Ref br) => ref_val br | _ => V)
    val _ = TYP:= T
  in
      print_value nam (!VAL);
      print_type  nam (!TYP)
  end;

end;

local

	val failwith = Utils.Except.failwith
	val bug = Utils.Except.bug

	open Utils.Timing

	val message = Printing.message 

	val legoprint   = Pretty.legoprint 
	val prnt_decl = Pretty.prnt_decl 
	val prnt_defn = Pretty.prnt_defn 
	val prnt_red = Pretty.prnt_red 
	val print_words = Pretty.print_words 

	open Term 

in 

  fun Dnf _ = (Namespace.Dnf(); message "DNF"; Pr())

  fun Hnf n = (Namespace.Hnf(); message "HNF"; Pr()) (* bug at n:int ? *)

  fun Normal _ = (Namespace.Normal(); message "Normalize"; Pr())

fun Expand path nams = (Namespace.Expand path nams;
			print_words ("Expand"::nams
				     @["relative","to","the","path",
				       ListFormat.fmt
				       {init="[",sep=",",final="]",
					fmt=Int.toString} path]);
		(* should be PR() for the 1.3.1.1 patch for ProofGeneral? *)
			Pr())

fun ExpAll path m = (Namespace.ExpAll path m;
		     print_words ("ExpAll "^Int.toString m::
				  ["relative","to","the","path",
				   ListFormat.fmt
				       {init="[",sep=",",final="]",
					fmt=Int.toString} path]);
		(* should be PR() for the 1.3.1.1 patch for ProofGeneral? *)
		     Pr()) 

fun Equiv trm_c =
    let
      val (mkVar,eraseNew,close) = Namespace.manageVars()
      val ((V,_),sbst) = Engine.EvalRefine mkVar trm_c (* 2011 *) 
    in
	(Namespace.Equiv sbst V; message"Equiv"; Pr())
    end;

fun Eval c =
  let
     val VT = Engine.EvalRefine0 c 
  in
      StoreVT VT
  end;

(* *** Evaluate contexts, reductions, defintional equalities *** *
 * *** unwrap on failure: used in lego-grm and Claire's code *** *)
exception DefnError (* for lego-grm *)

local
	(* 2011: refactor Namespace addBndGbl and its use here: fEvalCxt!!! *)
    fun evalCxt (pfx as Prefix(_,v,_,_,_),ns,c) = 
      let (* replace extendCxtGbl : ... -> context with addBndGbl : ... -> unit *)
      	fun eCG n = Namespace.addBndGbl Bnd pfx n (Engine.fEval c)
	val names = Utils.StringUtil.concat_space ns
      in case v
	   of Def => (List.app eCG ns; (* to get List.app here *)
	      	      let
			  val B = Namespace.topNamespace()
                   	  val V = (ref_val B)
		   	  val T = (ref_typ B)
		      in (* *** tests interactive () *** *)
			prnt_defn names V T 
		      end)
	    | _ => if Namespace.activeProofState()
		     then failwith"Cannot add assumptions during a proof"
		   else (List.app eCG ns; (* and to get List.app here *)
			 let
			  val B = Namespace.topNamespace()
		   	  val T = (ref_typ B)
		      	 in
			  prnt_decl v names T
		         end)
      end
in 

   fun EvalCxt_ cxt = 
   (* LegoUtils.TimerWrapper (Namespace.NSPrestoreWrapper (List.app evalCxt)) cxt *)
       let
           val t = start_timer()
	   val _ = Namespace.NSPWrapper (List.app evalCxt) cxt 
  	 in   message(print_timer t)
    	end
end;

fun EvalCxt cxt = EvalCxt_ (unCtxt cxt)

fun EvalDefn (v_c,cst) = 
    EvalCxt_ [(Prefix(Let,Def,UnFroz,Global,[]),[Concrete.getRefNam v_c],cst)]
    handle Concrete.getConcrete => raise DefnError

fun EvalRed reduc =
  if Namespace.activeProofState()
    then failwith"Cannot add reductions during a proof"
  else
    let
      val (fEred as (V,_)) = Engine.fEval reduc
      val _ = Namespace.SaveReductGbl fEred
      val _ = (prnt_red V; message"compiling reductions")
    in Namespace.MakeAllPats()
    end

local
  val t = ref (start_timer()) (* just one, since at toplevel, users can only ask for one *)
in
  fun StartTimer() = (t:= start_timer(); message"- Start Timer - ")
  fun PrintTimer() = message("- Print Timer - "^(makestring_timer (!t)))
end


(* ************************************* *)
(* file system utilities *)

fun PWD () = message(OS.FileSys.getDir())
fun CD dir = (OS.FileSys.chDir dir handle NotDirectory =>
	               		   message("Error: cannot find directory "^dir);
              message(OS.FileSys.getDir()
				   handle NotDirectory => dir))

(***  For dynamic changes to LEGOPATH ***)

local
  fun splitup([],l) = [implode (List.rev (#"/"::l))]
    | splitup(#":"::t, l) = (implode (List.rev (#"/"::l))) :: (splitup(t,[]))
    | splitup(c::t, l) = splitup(t, c::l)
  val addPath = ref ([]:string list)
  val delPath = ref ([]:string list)
in
  fun legopath() = case (OS.Process.getEnv "LEGOPATH") 
		   of 	  NONE 	 => ["./"]
		      | SOME (s) => splitup (explode s, []) 
end;

(* ************************************* *)

(* ******************************************************************* *)

(* 2011: need to shift type *)
type ind_options =
  {params:ctxt_c, constructors:ctxt_c, elimOver:cnstr_c,
   safe:bool, noReds:bool, double:bool, relation:bool,
   theorems: bool, inversion: bool};

val inductive_no_switches = {params=(mkCtxt []:ctxt_c), 
    			     constructors=(mkCtxt []:ctxt_c), 
			     elimOver=Concrete.mkRef_c"TYPE", safe=true, noReds=false,
			     double=false,
			     relation=false, theorems=false, inversion=false }

    fun inductive_datatype ct2 indopt  =
(* 
       let
          val oldcontext = Namespace.getNamespace()
          val
    	{params=p,constructors=c,elimOver=e,
    	 safe=s,noReds=nr,double=d,relation=r,theorems=t,
             inversion=i} = indopt
          val nr = nr orelse null c (* null required again!!! *)
          val do_inductive_type =
                if d then Double.do_inductive_type_double
    		     else if r then Relation.do_weak_inductive_type
    			      else Inductive.do_old_inductive_type
          val (ctxt1,reduc) = do_inductive_type s p ct2 c nr e
    	          handle Inductive.sch_err s => failwith ("Inductive: "^s)
          (* Claire's Theorems
          val ctxt2 = if t then (Inductive.do_just_theorems p ct2 c) else []
                  handle Inductive.sch_err s => failwith ("Theorems: "^s) *)
          (* stuff for picking out names of types being defined *)
          fun type_names [] = []
    	    | type_names ((_,_,_,_,l,_)::t) = l@(type_names t)
          val tns = type_names ct2
          fun bungInTypeLabel s = ((Namespace.addLabel ([s],s));
                                   (Namespace.addLabel ([s,"elim"],s^"_elim")))
          fun bungInConLabel c =
              let val (_,t) = Concrete.fEvalNam c
                  fun ty (Bind ((Pi,_),_,_,r)) = ty r
                    | ty (App ((f,_),_)) = ty f
                    | ty (Ref b) = ref_nam b
                    | ty _ = bug "bad constructor type slipped through"
              in  Namespace.addLabel ([ty t,c],c)
              end
        in
          ((EvalCxt ctxt1);
           (List.map bungInTypeLabel tns);
           (List.map bungInConLabel (type_names c));
           (if not nr then EvalRed reduc else ());
    	   (* Claire's Theorems  (if t then EvalCxt ctxt2 else ()); *)
    (* Conor's stuff goes here *)
           (if t then ((List.map ConorInductive.DoConorTheorems tns);()) else ());
           (if i then ((List.map ConorInductive.DoConorInversion tns);()) else ()))
          handle ex => (Namespace.putNamespace oldcontext; raise ex)
        end
*) 
   let 
      val {params=p,constructors=c,elimOver=e,safe=s,noReds=nr,
	   double=d,relation=r,theorems=t,inversion=i} = indopt 
      fun do_inductive_datatype ct = 
      	 let 
          (* stuff for picking out names of types being defined *)
            fun type_names        ([])  = []
    	      | type_names ((_,l,_)::t) = l@(type_names t)
(* 2011: need to shift type *)
            val uct = unCtxt ct 
            val uc  = unCtxt c  
            val tns = type_names (uct) 
            val tnc = type_names (uc) 

	    val nr = nr orelse null (uc) (* null required again!!! *)

            val do_inductive_type =
                if d then Inductive.do_inductive_type_double
    		     else if r then Inductive.do_weak_inductive_type
    			      else Inductive.do_old_inductive_type
            val (ctxt1,reduc) = do_inductive_type s p ct c nr e
    	          handle Inductive.sch_err s => failwith ("Inductive: "^s)
          (* *** Claire's Theorems ******************************************* *** *
            val ctxt2 = if t then (Inductive.do_just_theorems p ct c else []
           * ***        handle Inductive.sch_err s => failwith ("Theorems: "^s) *** *)
            fun bungInTypeLabel s = ((Namespace.addLabel ([s],s));
                                     (Namespace.addLabel ([s,"elim"],s^"_elim")))
            fun bungInConLabel c =
                let (* val (_,t) = Engine.fEvalNam c *)
		    val t = Engine.RefTyp_s c
                    fun ty (Bind ((Pi,_),_,_,r)) = ty r
                      | ty (App ((f,_),_)) = ty f
                      | ty (Ref b) = ref_nam b
                      | ty _ = bug "bad constructor type slipped through"
                in 
		   Namespace.addLabel ([ty t,c],c)
                end
	 in 
	    ((EvalCxt ctxt1);
             (List.map bungInTypeLabel tns);
             (List.map bungInConLabel tnc);
             (if not nr then EvalRed reduc else ());
    	     (* Claire's Theorems  (if t then EvalCxt ctxt2 else ()); *)
             (* Conor's stuff goes here *)
             (if t then ((List.map ConorInductive.DoConorTheorems tns);()) else ());
             (if i then ((List.map ConorInductive.DoConorInversion tns);()) else ()))

	 end 
   in 
      Namespace.NSPWrapper do_inductive_datatype ct2 
   end;

fun record_type ct2 indopt = 
(* ***
    let 
      val oldcontext = Namespace.getNamespace()
      val
	{params=p,constructors=c,elimOver=e,
	 safe=s,noReds=nr,double=d,relation=r,theorems=t,
             inversion=i} = indopt 
      val (ctxt1,reduc,ctxt2) = Record.do_record_type p ct2 c e
                     handle Record.sch_err s => failwith ("Inductive: "^s);
    in
      ((EvalCxt ctxt1;
	legoprint (#1 (Concrete.fEval reduc));
	EvalRed reduc;
       EvalCxt ctxt2)
      handle ex => (Namespace.putNamespace oldcontext; raise ex))
    end 
 * ***)

   let 
      val {params=p,constructors=c,elimOver=e,safe=s,noReds=nr,
	   double=d,relation=r,theorems=t,inversion=i} = indopt 

      fun do_record_type ct = 
         let 
      	    val (ctxt1,reduc,ctxt2) = Inductive.do_record_type p ct c e
                 handle Inductive.sch_err s => failwith ("Inductive: "^s);
	    val V = Engine.fEvalVal reduc
	 in 
	    (EvalCxt ctxt1;
	     EvalRed reduc; legoprint V ; 
	     EvalCxt ctxt2)
	 end
   in 
      Namespace.NSPWrapper do_record_type ct2
   end;


end;


    fun inductive_update_constructors constr
        {elimOver=e,safe=u,noReds=nr,double=d,params=p,relation=r,
         theorems=t,constructors=_,inversion=i}
        = {params=p,constructors=constr,elimOver=e,safe=u,noReds=nr,
           double=d,relation=r,theorems=t,inversion=i}
    
    fun inductive_update_params ctxt
        {constructors=c,elimOver=e,safe=u,noReds=nr,double=d,relation=r,
         theorems=t,params=_,inversion=i}
        = {params=ctxt,constructors=c,elimOver=e,safe=u,noReds=nr,
           double=d,relation=r,theorems=t,inversion=i}
    
    fun inductive_update_universe universe 
        ({safe=u,noReds=nr,double=d,params=p,relation=r,theorems=t,
          constructors=c,elimOver=_,inversion=i}:ind_options)
        = ({params=p,constructors=c,elimOver=universe,safe=u,
    	noReds=nr,double=d,relation=r,
        theorems=t,inversion=i}:ind_options)
    
    fun inductive_update_noreds
        {elimOver=e,safe=u,double=d,params=p,relation=r,theorems=t,
         constructors=c,noReds=_,inversion=i}
        = {params=p,constructors=c,elimOver=e,safe=u,noReds=true,
         double=d,relation=r,theorems=t,inversion=i}
    
    fun inductive_update_double
        {elimOver=e,safe=u,params=p,relation=r,theorems=t,constructors=c,
         noReds=nr,double=_,inversion=i}
        = {params=p,constructors=c,elimOver=e,safe=u,noReds=nr,
           double=true,relation=r,theorems=t,inversion=i}
    
    fun inductive_update_unsafe
        {elimOver=e,params=p,constructors=c,noReds=nr,double=d,
         relation=r,theorems=t,safe=_,inversion=i}
        = {params=p,constructors=c,elimOver=e,safe=false,noReds=nr,
           double=d,relation=r,theorems=t,inversion=i}
    
    fun inductive_update_theorems
        {elimOver=e,params=p,constructors=c,noReds=nr,double=d,
         relation=r,safe=u,theorems=_,inversion=i}
        = {params=p,constructors=c,elimOver=e,safe=u,noReds=nr,double=d,
           theorems=true,relation=r,inversion=i}
    
    fun inductive_update_relation
        {elimOver=e,params=p,constructors=c,noReds=nr,double=d,
         theorems=t,safe=u,relation=_,inversion=i}
        = {params=p,constructors=c,elimOver=e,safe=false,noReds=nr,
           double=d,relation=true,theorems=t,inversion=i}
    
    fun inductive_update_inversion
        {elimOver=e,params=p,constructors=c,noReds=nr,double=d,
         theorems=t,safe=u,relation=r,inversion=_}
        = {params=p,constructors=c,elimOver=e,safe=false,noReds=nr,
           double=d,relation=r,theorems=t,inversion=true}

end

