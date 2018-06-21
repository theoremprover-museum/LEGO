(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* Umachine.sml *)
(* Lescanne's weak/strong normalization on open terms *)

(* 21/Oct/98 Conor changes pattern compiler to expand local definitions *)

signature UMOPEN = 
  sig 

      type cnstr
      
    val UMnorm : cnstr -> cnstr
    val UMwhnf : cnstr -> cnstr
    val UMdnf  : cnstr -> cnstr
    val UMpnf  : cnstr -> cnstr
    val UMtype_match : cnstr -> cnstr -> bool

    val sameTerm : cnstr -> cnstr -> bool

(* *** for machine.sml *** *)
    val thryUMwhnf : cnstr -> cnstr

(* *** for unif.sml *** *)
    val rUMwhnf : cnstr -> cnstr Utils.Modif.modif
    val s1UMwhbenf : int -> cnstr -> cnstr Utils.Modif.modif

    val unifwhnfP : cnstr -> bool

(* *** for Init, Namespace *** *)
    val init_reductions :  unit -> unit
    val add_reductions  : cnstr -> unit

(* *** 2011: flags *** *)

    val um_debug : bool ref 
    val ae_debug : bool ref 
    val tm_debug : bool ref 
    val sp_debug : bool ref 
    val pat_debug : bool ref 
    val share_debug : bool ref 
    val dnf_debug : bool ref 
    val st_debug : bool ref 

    val liberal_matching_switch : bool ref 
    val pat_norm_switch : bool ref 

    val tm_debug_print: string -> ('a -> unit) -> 'a -> unit
    val tm_debug_report: string -> unit
  end

functor FunUMopen (structure Term : TERM
		   structure Subst : SUBST
		   structure LegoFormat : LEGOFORMAT
		   structure Pretty : PRETTY
		   sharing 
		   	   type Term.cnstr
			      = Subst.cnstr
			      = LegoFormat.cnstr
			      = Pretty.cnstr
		   and 
		   	   type Term.binding
			      = Subst.binding
		 ) 
(* *** *
structure UMopen 
 * *** *)
	: UMOPEN
 = 
struct

local 

      val bug = Utils.Except.bug 
      val failwith = Utils.Except.failwith 

      val assoc = Utils.ListUtil.assoc 

      val prs = Printing.prs
      val prnl = Printing.prnl
      val message = Printing.message

      val legoprint = Pretty.legoprint
      val print_expand = Pretty.print_expand
(*  *)
      open Term 

      val subst1 = Subst.subst1 

in 

	type cnstr = Term.cnstr 

val um_debug = ref false;
val ae_debug = ref false;
val tm_debug = ref false;
val sp_debug = ref false;
val pat_debug = ref false;
val share_debug = ref false;
val dnf_debug = ref false;
val st_debug = ref false;      (* sameTerm *)
      
fun flre opn = if (!st_debug) then opn() else ()

val liberal_matching_switch = ref true;
val pat_norm_switch = ref false; 

fun tm_debug_print (msg:string) prntr M = 
    if (!tm_debug) 
       then (prs msg;(prntr M))
    else ();

fun tm_debug_report msg = tm_debug_print "" message msg

(* move to term.sml *)

  fun sameTerm c d = (* a better equality test on type cnstr than polyEqual *)
    let

      val _ = flre (fn()=> (prs"**sT_deb t l: "; print_expand c;
			    prs"         t r: "; print_expand d))

      fun samTrm cd =
	case cd of
	  (Bind((bt1,_),_,l1,r1),Bind((bt2,_),_,l2,r2)) =>
	    (if bt1=bt2 then true
	     else (flre (fn()=> message"**sT_deb f: bind type"); false))
	    andalso samTrm (l1,l2) andalso samTrm (r1,r2)
	| (Ref br1,Ref br2) =>
	    if sameRef br1 br2 then true
	    else (flre (fn()=> message("**sT_deb f: Ref "^
				       (ref_nam br1)^" "^(ref_nam br2)));
		  false)
	| (Rel n1,Rel n2) =>
	    if n1=n2 then true
	    else (flre (fn()=> message("**sT_deb f: Rel "^
				       (Int.toString n1)^" "^(Int.toString n2)));
		  false)
	| (Tuple(t1,cs1),Tuple(t2,cs2)) =>
	    (samTrm(t1,t2) andalso List.all samTrm (ListPair.zipEq (cs1,cs2))
	     handle ListPair.UnequalLengths =>
	       (flre (fn()=> message"**sT_deb f: Tuple"); false))
	| (Type n1,Type n2) =>
	    if (Universes.univ_cmp n1 n2) (* 2011 *)
	      then true
	    else (flre (fn()=> message"**sT_deb f: TypeType"); false)
	| (Prop,Type _) =>
	    if (!Theories.LuosMode) then true
	    else (flre (fn()=> message"**sT_deb f: PropType"); false)
	| (Prop,Prop) => true
	| (Theory,Theory) => true
	| (App((f1,as1),_),App((f2,as2),_)) =>
	    (samTrm(f1,f2) andalso List.all samTrm (ListPair.zipEq (as1,as2))
	     handle ListPair.UnequalLengths =>
	       (flre (fn()=> message"**sT_deb f: App"); false))
	| (Proj(p1,t1),Proj(p2,t2)) =>
	    (if p1=p2 then true
	     else (flre (fn()=> message"**sT_deb f: proj"); false))
	    andalso samTrm(t1,t2)
	| (RedTyp(_,c1),RedTyp(_,c2)) => samTrm(c1,c2)
	| (Var(n,_),Var(m,_)) =>
	    if n=m then true
	    else (flre (fn()=> message("**sT_deb f: Var "^
				       (Int.toString n)^" "^(Int.toString m)));
		  false)
	| (LabVT(l1,c1,t1),LabVT(l2,c2,t2)) =>
	    (if l1=l2 then true
	     else (flre (fn()=> message"**sT_deb f: LabVT"); false))
	    andalso samTrm(c1,c2) andalso samTrm(t1,t2)
	| (CnLst cs1,CnLst cs2) =>
	    (List.all samTrm (ListPair.zipEq (cs1,cs2))
	     handle ListPair.UnequalLengths =>
	       (flre (fn()=> message"**sT_deb f: CnLst"); false))
	| (Bot,Bot) => bug"UM,samTrm;Bot"
	| (x,y) =>
	     (flre (fn()=> (prs"**sT_deb f l: "; print_expand x;
			    prs"         f r: "; print_expand y));
	      false)
    in 
	 Universes.tryUniverses samTrm (c,d)
    end;
(* *)

(* *** compiling reductions into the machine *** *)

(** patterns for the rewrite operations **)
datatype pat =
    Pcons of binding                               (* globals *)
  | Pmv of int                                     (* match vars *)
  | Papp of pat * (pat list)
  | Pprop
  | Ptype of Universes.node
(* print patterns for debugging *)
local
  val rec pp =
    fn Pcons(br) => prs (ref_nam br) (* Pcons(Bd{bd=(bv,s,c,d),...}) => prs s *)
     | Pmv(s) => prs("["^Int.toString s^"]")
     | Papp(p,args) =>
	 (prs"("; pp p; prs" ";
	  List.app (fn x => (pp x;prs" ")) args; prs")")
     | Pprop => prs"Prop"
     | Ptype(n) => prs"Type"
in
  fun print_pat pat = (pp pat; prnl())
end;

fun pat_head_const_args lhs p =
  case p
    of (Pcons br) => (br,0)
     | Papp(p',args) => (#1(pat_head_const_args lhs p'),length args)
     | _ => (prs"LHS of rewrite has no head constant: ";
	     legoprint lhs;
	     failwith"reductions not accepted")

type reduction = int*int*pat*cnstr (* nbr args, nbr match vars, LHS, RHS *)
type reductions = reduction list;

(** for hashing reductions on the binding, br, of the head Ref(br) of LHS **)
structure HashReds :
  sig
    val init_reductions : unit -> unit
    val add_reductions : reductions -> unit
    val find_reductions : binding -> reductions
  end =
  
struct
    (* first int is timestamp of the head constant *)
    type my_reds = int * reductions 
    val TableSize = 701
    val HashTable = (* entries are (my_reds list) in case of hash collision *)
      ref (Array.array(TableSize,nil) : (my_reds list) Array.array)

    fun init_reductions() = HashTable:= Array.array(TableSize,nil)

    fun hash (ts:int) = ts mod TableSize

    fun add_reduction (red as (_,_,lhs,_)) =
      let
	val (hbr,_) = pat_head_const_args Bot lhs
	val phc = ref_ts hbr
	val i = hash phc
	val old_i = Array.sub(!HashTable,i)
	fun same_key ((n,_):my_reds) =  phc = n
	val (this_one,others) = List.partition same_key old_i (* 1998: filter_split *)
	val _ = if (!pat_debug) then (prs"**add_red; "; print_pat lhs)
		else ()
	val new_this_one = case this_one
			     of [] => (phc,[red])
			      | [(_,reds)] => (phc,reds@[red])
			      | x => bug("add_reduction: "^Int.toString(length x))
      in  Array.update(!HashTable,i,new_this_one::others)
      end

    val add_reductions = List.app add_reduction

    fun find_reductions (br:binding) =
      let
	val tsbr = ref_ts br
	val all_iReds = Array.sub(!HashTable,hash tsbr)
      in
	assoc tsbr all_iReds handle Assoc => []
      end

end;  (*  struct HashReds  *)

(* ***************************************************************************** *)
(* compiling patterns *)
local 

      val succ = Utils.Counting.succ 
      val counter = Utils.Counting.counter 

(* Conor *)
    fun splatDefs (Bind ((Let,Def),_,dfn,bod)) = splatDefs (subst1 dfn bod)
      | splatDefs (Bind (bv,nam,dom,rng)) = Bind (bv,nam,dom,splatDefs rng)
      | splatDefs x = x

    exception StripLocs

    fun stripLocs mvars makeRhs =
      fn Bind((Lda,vis),n,lbl,bod) =>
           stripLocs (succ mvars) (fn x=> makeRhs (Bind((Lda,vis),n,lbl,x))) bod
       | CnLst pairs => (mvars,makeRhs,pairs)
       | _ => raise StripLocs 

in    

fun makePats nf c = (* 2011: lifted out the nf function *)
  let
    val _ = if (!pat_debug) 
    	       then (prs"**pat_deb; ";Pretty.prnt_red c)
	    else ()

    val (mvars,makeRhs,pairs) = stripLocs 0 (fn x => x) (splatDefs c)
    			        handle StripLocs => 
				       (prs"not a pattern: ";print_expand c;
	       			        failwith"not a pattern")


    val timestamp = counter mvars (* starts after the number of match vars *)

    fun mp (Rel n,_) = Pmv n
      (* The argument of type prntVisSort is because implicit arguments are
       * matched as "anonymous variables".  This is because of the inferred
       * arguments of the recursor of an inductive relation.  *)
      | mp (c,ShowNorm) =
	       (case c of
		  App((f,aa),vs) =>
		    Papp(mp (f,ShowNorm),List.map mp (ListPair.zipEq (aa,vs)))
		| Ref br => Pcons(br)
		| Prop => Pprop
		| Type n => Ptype(n)
		| c => (print_expand c;failwith"illegal pattern"))
      | mp _ = Pmv (timestamp())

    fun mpp (LabVT(RedPr,lhs,rhs)::rest) 
      = 
           let
	     val nlhs = nf lhs (* 2011: lifted out the nf function *)
	     val _ = if (!pat_debug) 
	     	     	then (prs"**pat_deb:mpp, lhs ";print_expand nlhs)
		     else ()
	     val plhs = mp (nlhs,ShowNorm)
	     val (hc,args) = pat_head_const_args lhs plhs
	   in  (args,mvars,plhs,makeRhs rhs)::(mpp rest)
	   end
      | mpp [] = []
      | mpp _ = bug"makePats2"

  in

    mpp pairs

  end
end;

(* *** end of compiling reductions *** *)

(* now we begin the Umachine! *)

(* first, some switches for the various algorithms *)
datatype dfnFlgs = DF of {beta:bool,gdfn:bool,ldfn:bool,spdfn:bool}

fun gdfn (DF{gdfn=b,...}) = b
fun beta (DF{beta=b,...}) = b
fun ldfn (DF{ldfn=b,...}) = b
fun spdfn (DF{spdfn=b,...}) = b

val trueDF = DF{beta=true,gdfn=true,ldfn=true,spdfn=true}

val normDF = trueDF
                                             (** spdfn false ?? **)
val dnfDF  = DF{beta=true, gdfn=false,ldfn=false,spdfn=true}
val pnfDF  = DF{beta=false,gdfn=false,ldfn=false,spdfn=false}

val unifDF = trueDF (* !!! for Unif !!! *)
val s1beDF = DF{beta=true,gdfn=false,ldfn=true,spdfn=false}

(* substitution can't change this sound but incomplete test for whnf *)
fun whnfP (dfnf:dfnFlgs) c =
  let
    fun Prec x =
    case x of
      Bind((bt,_),_,_,_) => bt<>Let orelse not (ldfn dfnf)
    | Ref br => not (gdfn dfnf andalso ref_isDefnNow br) andalso
	(not (spdfn dfnf) orelse null(HashReds.find_reductions br))
    | Rel _ => true
    | Tuple _ => true
    | Type _ => true
    | Prop => true
    | Theory => true
    | App((f,_),_) => Prec f andalso not (isLda f)
    | Proj(_,t) => Prec t andalso not (isTuple t orelse isThry t)
    | RedTyp(_,t) => Prec t
    | Var _ => false
    | LabVT _ => bug"UM,whnfP;LabVT"
    | CnLst _ => bug"UM,whnfP;CnLst"
    | Case _ => bug"UM,whnfP;Case"
    | Bot => bug"UM,whnfP;Bot"
  in Prec c
  end

(* now the Umachine proper         *
 * lots of mutual data structures! *
 * lots of mutual recursion        *)

datatype 
    closure = Clos of (cnstr * env)
and 
    envClos = EC of closure | Shift
and 
    stackClos = SC of (closure * stack) ref * prntVisSort
    	      | SFST
	      | SSND
	      | SLBL of string * closure
withtype 
    env = (envClos * int) list
and 
    stack = stackClos list;

(* the UM is a state machine *)

type state = bool * env * stack * cnstr;

(**  helpers for the eventual tail recursion  **)

   val nilE = [] : env

   val nilS = [] : stack

   fun mkClos0 c = Clos(c,nilE) : closure 

   fun mkStk0 cl = (cl,nilS) : closure * stack

   fun mkClosStk0 c = mkStk0 (mkClos0 c) : closure * stack

(**  for debugging  **)

local 

    val prnt = Pretty.prnt 
    fun prnt_tm mrk t = (prs mrk ; prnt t)
    fun prnt_n mrk n = prs(mrk^(Int.toString n)^" ")

in 

fun prntenv (e:env) =
  let val aux =
	fn (EC(Clos cl),n) =>
	     ((case cl of
		(t,[]) => prnt_tm " !" t (* prs" !"; prnt t; prs(","^(Int.toString n)^" ")*)
	      | (t,_)  => prnt_tm " *" t (* prs" *"; prnt t; prs(","^(Int.toString n)^" ")*)
	      ); prnt_n "," n )
	 | (Shift,n) => prnt_n " ^" n (* prs(" ^"^(Int.toString n)^" ") *)
  in  prs"env "; List.app aux e; prnl()
  end

fun prntstack (s:stackClos list) =
  let val aux =
    fn SC(Cl,_) =>
        ((case !Cl of
	   (Clos(t,[]),[]) => prnt_tm " !" t
	 | (Clos(t,_),_)   => prnt_tm " *" t
	 ); prs" ")
     | SFST => prs" Fst "
     | SSND => prs" Snd "
     | SLBL(s,_) => prs("."^s)
  in  prs"stk "; List.app aux s; prnl()
  end

end; 

(**  for debugging  **)

fun prntDfnFlgs (DF{beta,gdfn,ldfn,spdfn}) =
  "("^Bool.toString beta^","^Bool.toString gdfn^","^
  Bool.toString ldfn^","^Bool.toString spdfn^")";


(**  a helper function enriched with debugging info.   **)

fun Share cl ces =
  let
    val _ = if (!share_debug) 
    	       then (let
			val (Clos(ot,_),_) = !cl
		   	val (Clos(nt,_),_) = ces
		     in (prs"**share_deb: old ";legoprint ot;
		     	 prs"**share_deb: new ";legoprint nt)
		     end)
	    else ()
  in
    cl:= ces
  end

(**  now we start computing...  **)

local (* 2011: some simple code motion, to simplify (???) *)

      open Utils.Modif

      val succ = Utils.Counting.succ 
      val pred = Utils.Counting.pred 

(* optimise lifting the environment and appending the new item
 * on the back
 *)
   fun gen_lft_env (n:int) cs =
     let fun le [] = cs
   	   | le ((c,i)::e) = (c,n+i)::le e
     in le
     end
   fun lft_app e d = gen_lft_env 1 [(d,0)] e
   fun lft_env e   = gen_lft_env 1 [] e

fun acc_env (n,env) : closure =
  let
    val ShZe = (Shift,0);
    fun mkClosRel n = mkClos0 (Rel n) 
    val _ = if (!ae_debug) 
    	       then (prs("**ae_debug; "^(Int.toString n)^": "); prntenv env)
	    else ()
    fun Rel1 env : closure =      (* n=1  *)
      let 
	val _ = if (!ae_debug) 
	      	   then (prs("**ae_debug1: "); prntenv env)
		else ()
      in case env
	   of [] => mkClosRel 1 (* Clos(Rel 1,[]) *)
	    | (c,m)::e =>
		(if m>0 then (Rel1 e : closure)
		 else case c of
		   Shift => (acc_env(2,e) : closure)
		 | EC(Cl as (Clos(a,f))) => (* if e=[] then Cl else Clos(a,f@e) *)
		     case (e,a)
		       of ([],_) => Cl
			| (_,Rel i) => acc_env (i,f@e)
			| _ => Clos(a,f@e))
      end
    (* n>1, env non-empty, only grows *)
    fun nSuc c : int * int * (envClos * int) list -> closure = 
      let
	fun aux (n,i,e) : closure =
	  case i
	    of 0 => (acc_env((case c of Shift => succ n | _ => pred n),e) : closure) 
	       	    	     (* 1998 : if c=Shift then n+1 else n-1 *)
	     | m => let val j = m-1
		    in if n>2 then (aux(n-1,j,ShZe::e) : closure)
		       else (Rel1((c,j)::ShZe::e) : closure)
		    end
      in aux
      end
  in
    (case env of
       [] => mkClosRel n (* (Clos(Rel n,[]) : closure) *)
     | (Shift,0)::e => (acc_env(n+1,e) : closure)
     | (c,i)::e => if n=1 then (Rel1 env : closure) else (nSuc c (n,i,e) : closure)
	 : closure)
  end

fun evalState (Clos(t,e),p) =
  let
    fun unwArgs (t,stk) =
      let
	fun aux (cls,trm) = case cls (* 2011: List.foldl *)
	  of SC(cl,v)  => MkApp((trm,[evalState (!cl)]),[v])
	   | SFST      => (MkProj(Fst,trm))
	   | SSND      => (MkProj(Snd,trm))
	   | SLBL(s,_) => (MkProj(Labl(s),trm))    (* use trm or cl ? *)
      in  List.foldl aux t stk (* 2011: List.foldl *)
      end
  in
    case e of
      [] => unwArgs (t,p)
    | _ => let fun sbstClos e =
	fn Rel n => evalState(acc_env(n,e),[])
	 | App(bod) => umkApp (sbstClos e) bod
	 | Bind(x,y,l,r) => MkBind(x,y,sbstClos e l,sbstClos (lft_env e) r)
	 | Tuple(bod) => umkTuple (sbstClos e) bod
	 | CnLst(bod) => umkCnLst (sbstClos e) bod
	 | Proj(bod) => umkProj (sbstClos e) bod
	 | RedTyp(bod) => umkRedTyp (sbstClos e) bod
	 | Var(bod) => umkVar (sbstClos e) bod
	 | LabVT(bod) => umkLabVT (sbstClos e) bod
	 | t => t
	   in unwArgs(sbstClos e t,p)
	   end
  end

(* multiple beta-steps at once to avoid repeated lift_env *)
fun lda_bet_star (env,stk,t) =
  let
    fun count (SC(Cl,_)::stk,Bind((Lda,_),_,_,c),args) = count (stk,c,(!Cl)::args)
      | count x = x
    val (nstk,nc,args) = count (stk,t,[])
    fun env_args (Sn as (n,eargs)) =
      fn [] => Sn
       | (c,[])::args => env_args (n+1,(EC c,n)::eargs) args
       | cp::args => env_args (n+1,(EC(mkClos0(evalState cp)),n)::eargs) args
    val (n,eargs) = env_args (0,[]) args
  in
    (true,gen_lft_env n eargs env,nstk,nc)
  end

(* helper function for sgwhnf *)
fun unload ((prog,env,stk,t):state) : cnstr modif =
  let
    val ans = if prog then Mod(evalState(Clos(t,env),stk))
	      else UMod
    val _ = if (!um_debug) 
    	       then (prs"**unload_debug; output ";
		     case ans
		       of UMod   => message"no progress"
		        | Mod(t) => print_expand t)
	    else ()
  in  ans
  end

(* end of helper functions, previously mutually defined *)

in 

(* now the slightly simplified (* 2011 *) huge mutual definition *)

(* we have seperate flags to set whether to make progress or not on
 * global defns, local defns, and special defns.  We also take a set
 * of flags to update the working flags the first time progress is made,
 * so as to support expanding one defn, then only beta-redexes
 *)
(* thrydfn tells whether or not to expand a defn whose value is a theory
 * when it is not the subject of a projection
 *)
(* forceWindup tells whether or not to build the environment even if the
 * term is a whnf.  We force if we intend to go under a binder as in
 * computing a normal form or dnf
 *)
(* stopTS says to stop reducing if some progress has been made, and the
 * head constant has this timestamp. *)

fun UM (stopTS:int)
       (forceWindup:bool,thrydfn:bool) (dfn:dfnFlgs,stpDfn:dfnFlgs)
       ((PROG,ENV,STK,TRM):state) : state =
  let
    val curDfn = ref dfn
    val _ = if (!um_debug) 
    	       then (message("**UM_debug; "^(Bool.toString thrydfn)^", "^
			 	(Bool.toString (whnfP dfn TRM))^", "^
			 	 prntDfnFlgs dfn^", "^prntDfnFlgs stpDfn);
		     print_expand TRM)
	    else ()

    (** ref for toplevel progree ?? **)
    fun um (state as (prog:bool, env:env, stk:stack, t:cnstr):state) : state =
      let
	val _ = if (!um_debug) 
	      	   then (prs("**um_debug; input "^(Bool.toString prog)^", ");
		         print_expand t; prntenv env; prntstack stk)
		else ()
	(* if progress was made, swap dfn flags *)
	fun showProgress() = (curDfn:= stpDfn; true)
	fun stop st = st
	fun special br =
	  let
	    exception nomatch
	    fun raise_nomatch s =
	      (if (!sp_debug) 
	      	  then (message("**sp_deb; nomatch: "^s))
	       else ();
	       raise nomatch)
	    fun args_from_stk x =
	      case x
		of ([],stk) => ([],stk)
		 | (pa::pas,(sc as (SC _))::stk) =>
		     (case args_from_stk(pas,stk)
			of (zips,stk) => ((sc,pa)::zips,stk))
		 | _ => raise_nomatch("stack too short")

	    val spProg = ref prog  (** ref for toplevel progree ?? **)

	    val reds = HashReds.find_reductions br

	    val _ = if (!sp_debug) 
	    	       then (message("**sp_deb; head= "^ref_nam br^
				     ", nbr reds= "^Int.toString (length reds));
			     if null reds then ()
			     else (prntenv env; prntstack stk))
		    else ()

	    fun UMclos brp = UM brp (true,false) (trueDF,trueDF)

	    fun buildMatch (clspat,menv) =  (case clspat (* 2011: List.foldl *)
	      of (SC(Cl,_),Pmv s) =>  (* repeated vars ok in match if convertible *)
	         let val cl = !Cl
		 in  ((if UMtm cl (assoc s menv) then menv (* can change UVARS *)
		       else raise_nomatch("non-linear arg fails: "^Int.toString s))
		      handle Assoc => (s,cl)::menv)
		 end
	       | (SC(Cl,_),p) =>
		   (* when p not Pmv, c is computed for the right constructor *)
		   let
		     val ts = case p
				of Pcons brp => ref_ts brp
				 | Papp(Pcons brp,_) => ref_ts brp
				 | _ => ~1
		     val (Clos(c,e),s) = !Cl
		     val (prog,env,stk,c) = UMclos ts (prog,e,s,c)
		     val _ = spProg := (!spProg orelse prog)
		     val _ = Share Cl (Clos(c,env),stk)
		   in
		     case (stk,c,p) of
		       (_,Ref brc,Pcons brp) =>
			 if sameRef brc brp then menv
			 else raise_nomatch("different constructors: "^
					    ref_nam brc^", "^ref_nam brp)
		     | (stk,Ref brc,Papp(Pcons brp,pas)) =>  (***)
			 if sameRef brc brp
			   then
			     let
			       val (pairs,nstk) = args_from_stk (pas,stk)
			       val _ = if null nstk then ()
				       else bug"buildmatch;too many args"
			     in  List.foldl buildMatch menv pairs (* 2011: List.foldl *)
			     end
			 else raise_nomatch("different constructors: "^
					    ref_nam brc^", "^ref_nam brp)
		     | (_,Prop,Pprop) => menv
		     | (_,Type n,Ptype m) =>
(* univ_equal?  *)	 if Universes.node_equal n m then menv else raise nomatch 
(* no: see UMtm *)
		     | _ => raise_nomatch"different shape"
		   end
	       | _ => bug"buildMatch: other")

	    fun menv2stk (menv,m) =
	      let
		fun me2s M stk =
		  if m<M then stk
		  else 
		    let val cl = assoc M menv
		      handle Assoc => mkClosStk0 Bot (* (Clos(Bot,[]),[]) *)
		    in  me2s (M+1) (SC(ref cl,NoShow)::stk)
		    end
	      in  me2s 1
	      end

	    fun specrec [] = stop(!spProg,env,stk,t) : state
	      | specrec ((n,m,p,c)::rest) =
		(let
		   val _ = if (!sp_debug) 
		       	      then (message("**sp_deb; try reduction, args= "
					     ^Int.toString n^", #matchvars= "
					     ^Int.toString m);
				    prs"LHS: "; print_pat p;
				    prs"RHS: "; legoprint c)
			   else ()
		   val (nstk,nc) =
		     case p of
		       Pcons _ => (menv2stk ([],m) [],c)
		     | Papp(_,pas) =>
			 let
			   val (pairs,nstk) = args_from_stk (pas,stk)
			   val menv = List.foldl buildMatch [] pairs (* 2011: List.foldl *)
			 in (menv2stk (menv,m) nstk,c)
			 end
		     | _ => bug"specrec:illegal pattern"
		   val _ = if (!sp_debug) 
		       	      then (message("**sp_deb; special succeeds for "
					    ^ref_nam br))
			   else ()
		 in um(showProgress(),nilE,nstk,nc)     (* env MUST be nil *)
		 end handle nomatch => specrec rest)
    	  in specrec reds
	  end (* of special *)

	fun caseApp ((c,cs),vs) =
	  let
	    fun pa c =
	      case c of
		Ref br => mkClos0 c (* Clos(c,[]) *)
	      | Rel n  => acc_env(n,env)
	      | Prop   => mkClos0 c 
	      | Type _ => mkClos0 c 
	      | Theory => mkClos0 c 
	      | _      => Clos(c,env)
	    fun aux ((c,v):cnstr*prntVisSort,(s:stack)) : stack =
	      SC(ref(mkStk0(pa c)),v)::s
	  in
	    um (prog,env,List.foldr aux stk (ListPair.zipEq(cs,vs)),c)
	  end

	fun caseBind (bv as (bt,_),nam,l,r) =
	  case (stk,bt) of
	    (_,Let) =>                      (* local definition *)
	      if ldfn(!curDfn)
		then um(showProgress(),lft_app env (EC(Clos(l,env))),stk,r)
	      else stop(state)
	  | ([],_) => stop(state)            (* in whnf *)
	  | (_::_,Lda) =>                    (* beta redexes *)
	      if beta (!curDfn)
		then (showProgress(); um(lda_bet_star(env,stk,t)))
	      else stop(state)
	  (* project from theory: only if global defn's expanded *)
	  | (SLBL(s,cl)::stk',Thry) =>
	      let
		fun assoc (LabVT(Name l,a,_)::rest) =
		       if s=l then a else assoc rest
		  | assoc _ = bug"um:Bind:assoc"
		val lvts = case r
			     of CnLst lvts => lvts
			      | _ => bug"um:Bind,Thry"
	      in 
		um(showProgress(),lft_app env (EC cl),stk',assoc lvts)
	      end
	  (* *************************** *
	  (* project from parameterised theory *)
	  | (SLBL(s,cl)::stk',Lda) =>
	    um(showProgress(),env,stk',Bind(bv,nam,l,Proj(Labl s,r)))
	   * *************************** *)
	  | _ => bug"um: Bind"

	fun caseRef br =      (** all definitions are closed: forget env **)
	  if prog andalso stopTS=ref_ts br then stop(state)
	  else if ref_isDefnNow br andalso gdfn(!curDfn)
		 then um (showProgress(),nilE,stk,ref_VAL br)
	       else if ref_isDefn br orelse not (spdfn(!curDfn))
		      then stop(state)
		    else special br    (* try rewrite *)

	fun caseRel n =
	  case acc_env(n,env) of
	      Clos(relm as (Rel _),[]) => stop(prog,nilE,stk,relm)
	    | Clos(a,e) => um(showProgress(),e,stk,a)

	fun caseProj (p,c) =
	  case p of
	    Fst => um(prog,env,SFST::stk,c)
	  | Snd => um(prog,env,SSND::stk,c)
	  (* theory projection is like defn expansion *)
	  | Labl(s) => if gdfn(!curDfn)
			 then um(prog,env,SLBL(s,Clos(c,env))::stk,c)
		       else stop(state)

	fun caseTuple (T,cs) =
	  case (stk,cs)
	    of (SFST::nstk,l::_) => um(showProgress(),env,nstk,l)
	     | (SSND::nstk,_::[r]) => um(showProgress(),env,nstk,r)
	     | (SSND::nstk,l::ls) =>
		 (case gUMwhnf env T (* 2011: Tuples always need whnf!!! *)
		    of Bind(_,nm,_,S) => 
		      um(showProgress(),env,nstk,MkTuple(subst1 l S,ls))
		     | _ => bug"um: type of tuple")
	     | _ => stop(state)

	fun caseCase _ = bug"UM case" (* *** *)

      in

	case t of
	  App bod	=> caseApp bod
	| Bind bod 	=> caseBind bod
	| Ref bod 	=> caseRef bod
	| Rel n 	=> caseRel n
	| Proj bod 	=> caseProj bod
	| Tuple bod    	=> caseTuple bod
	| Case bod     	=> caseCase bod
	| LabVT(_,v,_) 	=> um(showProgress(),env,stk,v)  (* progress?? *)
	| _ => stop(state)
      end (* of um *)
  in if         not forceWindup 
     	andalso 
     		null ENV 
	andalso 
		null STK  
	andalso 
		whnfP dfn TRM
	then (PROG,ENV,STK,TRM)
     else um(PROG,ENV,STK,TRM)
  end (* of UM *)

and sgwhnf stopTS thrydfn (dfn:dfnFlgs) (stpDfn:dfnFlgs)
                   (env:env) (t:cnstr) : cnstr modif =
  unload (UM stopTS (false,thrydfn) (dfn,stpDfn) (false,env,nilS,t))

and gwhnf thrydfn (dfn:dfnFlgs) (env:env) (t:cnstr) : cnstr =
  case sgwhnf ~1 thrydfn dfn dfn env t
    of UMod => t
     | Mod(c) => c

and gUMwhnf env c = gwhnf false trueDF env c

and thryUMwhnf env c = gwhnf true trueDF env c
(*
and UMwhnf = gUMwhnf nilE
 *)
and UMtm (Clos(c1,e1),p1) (Clos(c2,e2),p2) =

  let

    fun tm LMflg (pM,pN) (envM,envN) (MN as (M0,N0)) =
      let
	val nilSS = (nilS,nilS)

	val UMclos = UM ~1 (true,false) (trueDF,trueDF)

	val ((_,envM,stkM,M),(_,envN,stkN,N)) =
	  (UMclos (false,envM,pM,M0),UMclos (false,envN,pN,N0))

	val tm_equal = tm false nilSS (envM,envN)
	val tm_cumul = tm LMflg nilSS (envM,envN)
	val tm_cumul_lft = tm LMflg nilSS (lft_env envM,lft_env envN)
(* 
	val _ = if (!tm_debug) 
	      	   then (message"** UMtm_debug **";legoprint M;legoprint N)
	        else ()
 *)
	val _ = tm_debug_report "** UMtm_debug **"
	val _ = tm_debug_print "" legoprint M
	val _ = tm_debug_print "" legoprint N

	val tmStk =
	  fn (SC(Cl1,_),SC(Cl2,_)) =>
	  (case (!Cl1,!Cl2) of ((Clos(c1,e1),p1),(Clos(c2,e2),p2)) =>
	     tm LMflg (p1,p2) (e1,e2) (c1,c2))
	   | (SFST,SFST) => true
	   | (SSND,SSND) => true
	   | (SLBL(s1,_),SLBL(s2,_)) => s1=s2
	   | _ => false
      in
	(case (M,N) of
	   (Type i,Type j) => Universes.univ_cmp_ LMflg i j (* 2011 *)
	 | (Prop,Type j) => LMflg
	 | (Prop,Prop) => true
	 | (Rel n,Rel m) => n=m
	 | (Ref(b1),Ref(b2)) => sameRef b1 b2
	 | (Bind((bt1,vs1),_,M1,M2),Bind((bt2,vs2),_,N1,N2)) =>
	     bt1=bt2 andalso
	     (case bt1 of
		Pi =>
		  (!liberal_matching_switch orelse vs1=vs2) andalso
		  tm_equal (M1,N1) andalso
		  tm_cumul_lft (M2,N2)
	      | Sig =>
		  tm_cumul (M1,N1) andalso
		  tm_cumul_lft (M2,N2)
	      | Lda =>   (**  ??? bug  ??? **)
		  tm_equal (M1,N1) andalso
		  tm_cumul_lft (M2,N2)
	      | Thry => bug"UMtype_match: Thry"
	      | Let => bug"UMtype_match: Let")
	 | (Tuple(T1,ls1),Tuple(T2,ls2)) => 
	     (tm_equal (T1,T2) andalso
	      List.all (tm_equal)
	      (ListPair.zipEq(ls1,ls2)) handle ListPair.UnequalLengths => false)
	 | (CnLst ls1,CnLst ls2) => 
	     (List.all (tm_equal)
	      (ListPair.zipEq(ls1,ls2)) handle ListPair.UnequalLengths => false)
	 | (LabVT(s1,v1,t1),LabVT(s2,v2,t2)) =>
	     s1=s2 andalso
	     tm_equal (v1,v2) andalso
	     tm_equal (t1,t2)
	 | (Var(n,_),Var(m,_)) => n=m
	 | (App _,App _) => bug"UMtype_match;App"
	 | (Proj _,Proj _) => bug"UMtype_match;Proj"
	 | _ => false)
	   andalso
	   (List.all tmStk (ListPair.zipEq(stkM,stkN))
	    handle ListPair.UnequalLengths => false)
      end
  in
     Universes.tryUniverses (tm (!Theories.LuosMode) (p1,p2) (e1,e2)) (c1,c2)
  end

(* now the UM-based normaliser *)
fun gnorm (dfn:dfnFlgs) : cnstr -> cnstr =
  let
    fun gndfn (p:stack) (env:env) (t:cnstr) : cnstr =
      let
	val _ = if (!dnf_debug) 
	      	   then (prs"**dnf_deb: ";
		   	 print_expand t;
		       	 prntenv env; prntstack p)
		else ()
	val (_,env,stk,hd) =  UM ~1 (true,false) (dfn,dfn) (false,env,p,t)
	val hd =
	  case hd of
	    Bind(bt,y,l,r) =>
	      MkBind(bt,y,gndfn0 env l,gndfn0 (lft_env env) r)
	  | Tuple bod => umkTuple (gndfn0 env) bod
	  | CnLst bod => umkCnLst (gndfn0 env) bod
	  | LabVT bod => umkLabVT (gndfn0 env) bod
	  | Proj bod  => umkProj (gndfn0 env) bod
	  | RedTyp bod => umkRedTyp (gndfn0 env) bod
	  | Var bod   => umkVar (gndfn0 env) bod
	  | _ => hd
	fun evcl Cl = case !Cl of (Clos(c,e),p) => gndfn p e c
	fun aux (cls,trm) = (case cls (* 2011: List.foldl *)
	  of SC(cl,v) => MkApp((trm,[evcl cl]),[v])
	   | SFST     => (MkProj(Fst,trm))
	   | SSND     => (MkProj(Snd,trm))
	   | SLBL(s,cl) => (MkProj(Labl(s),trm)))
	val ans = List.foldl aux hd stk (* 2011: List.foldl *)
	val _ = if (!dnf_debug) 
	      	   then (prs"**dnf_deb: output ";print_expand ans)
		else ()
      in  ans
      end

    and gndfn0 (env:env) (t:cnstr) : cnstr  = gndfn nilS env t

  in 

     gndfn0 nilE

  end

end; (* local defn of helper functions gen_lft_env through unload *)

end; (* local printers *) 

(* ***************************************************************************** *
 * exports *
 * ***************************************************************************** *)

(* for Unif: unifwhnfP, rUMwhnf and s1UMwhbenf  *)
val unifwhnfP = whnfP unifDF

val rUMwhnf = sgwhnf ~1 false unifDF unifDF nilE

(* one step then to whbenf *)
fun s1UMwhbenf stopTS = sgwhnf stopTS false unifDF s1beDF nilE

(* for Machine: thryUMwhnf *)
(* special for typechecking theory projections *)
val thryUMwhnf = thryUMwhnf nilE

(* main functions used everywhere *)
val UMwhnf = gUMwhnf nilE

val UMnorm = gnorm normDF

val UMdnf  = gnorm dnfDF

val UMpnf  = gnorm pnfDF 

fun UMtype_match c d = UMtm (mkClosStk0 c) (mkClosStk0 d) 

(* *** now can add reductions *** *)

val add_reductions = HashReds.add_reductions o 
    (makePats (if (!pat_norm_switch) then UMnorm else UMdnf)) (* 2011: simplify?! *)
val init_reductions = HashReds.init_reductions 

(* *** end of reductions *** *)

val _ = LegoFormat.whnfr:= UMwhnf; (* now printing is correct *)

end;  (* structure UMopen *)

(* open UMopen; *)

