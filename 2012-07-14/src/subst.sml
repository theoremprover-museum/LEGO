(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* * subst.sml   object langage substitution for cnstr terms * *)

(** Substitution of object language (nameless variable) terms **)
(** Remark : use sharing/modif for the substitution functions **)

functor FunSubst (structure Term:TERM
		  structure Pretty : PRETTY
		  sharing 
		   	   type Term.cnstr
			      = Pretty.cnstr
		  and 
		   	   type Term.binding
			      = Pretty.binding
		  ) 
(* *** *
structure Subst 
 * *** *)
	: SUBST 
 =

struct 

(* from unif.sml *)

local 

      val legoprint = Pretty.legoprint 

      open Utils.Modif 
      open Term

      val assoc = Utils.ListUtil.assoc
      val mem_assoc = Utils.ListUtil.mem_assoc

      val bug = Utils.Except.bug 

in 

      type cnstr = Term.cnstr
      type binding = Term.binding

(** existential variables: substitutions **)

      type assignment = int * cnstr;
      type substitution = assignment list;

      val nilS : substitution = [];

      val dom = mem_assoc; 

      fun unSubst  sub =  sub ;

      fun mkAssign ass =  ass ;
      fun mkSubst1 ass = [ass];

(* substitute for Rel(1) *)
(* vsub: M[N/0] *)

fun subst1 a : cnstr -> cnstr = 
  let
    fun subrec k : (cnstr -> cnstr Utils.Modif.modif) = 
      let
	val mem = ref (nilS)
	val closFlg = ref false
        fun mem_lift() = 
	  let val m = k - 1
	  in  if !closFlg then a else Utils.ListUtil.assoc m (!mem)
		   handle _ =>       (* call to lift_unshared tests a closed *)
		     case lift_unshared m a
		       of UMod => (closFlg:=true; a)           (* closed *)
			| (Mod a') => (mem:= (m,a')::(!mem); a')
	  end
      in
	fn Rel(n)   => if n = k then Mod(mem_lift())
			else if n < k then UMod else Mod(Rel(n - 1))
	 | App(b)    => (mkApp (subrec k) b)(*:cnstr modif*)
(* 2011: suppress debugging *)
	 | thry as Bind(b as ((Thry,_),_,_,_)) =>
	     ((* if (!theory_debug) 
	     	 then (prs"\n##thry_debug:subst1 in ";legoprint thry)
	      else ()*)
	      thry_debug "\n##thry_debug:subst1 in " legoprint thry;
	      mkBind subrec k b)
(* *)
	 | Bind(b)   => mkBind subrec k b
	 | Tuple(b)  => mkTuple (subrec k) b
	 | CnLst(b)  => mkCnLst (subrec k) b
	 | Proj(c)   => mkProj (subrec k) c
	 | RedTyp(c) => mkRedTyp (subrec k) c
	 | LabVT(b)  => mkLabVT (subrec k) b 
	 | _         => UMod
      end
  in share (subrec 1) end

(* an optimisation: substitution of a closed term *)
(* safe vsub: M[N/0] when N is Vclosed *)

fun subst1closed a = 
  let fun subrec k = 
    fn Rel(n)   => if n = k then Mod(a)
		   else if n < k then UMod else Mod(Rel(n - 1))
     | App(b)   => mkApp (subrec k) b
(* 
     | thry as Bind(b as ((Thry,_),_,_,_)) =>
	 ((* if (!theory_debug) 
	     then (prs"\n##thry_debug:subst1closed in ";legoprint thry)
	  else ()*)
	  thry_debug "\n##thry_debug:subst1closed in " legoprint thry;
	  mkBind subrec k b)
 *)
     | Bind(b)  => mkBind subrec k b
     | Tuple(b) => mkTuple (subrec k) b
     | CnLst(b) => mkCnLst (subrec k) b
     | Proj(b)  => mkProj (subrec k) b
     | RedTyp(b)=> mkRedTyp (subrec k) b
     | LabVT(b) => mkLabVT (subrec k) b
     | _        => UMod
  in share (subrec 1) end

(* from discharge.sml *) 
fun expandRef_as_needed P = 
    fn (rbr as (Ref br)) =>
        if ref_isDefn br andalso (P br)
	   then (expandRef_as_needed P) (ref_VAL br) 
	else rbr
     | (App b)   => umkApp   (expandRef_as_needed P) b
     | (Bind b)  => umkBind2 (expandRef_as_needed P) b
     | (Tuple b) => umkTuple (expandRef_as_needed P) b
     | (CnLst b) => umkCnLst (expandRef_as_needed P) b
     | (Proj b)  => umkProj  (expandRef_as_needed P) b
     | (RedTyp b)=> umkRedTyp (expandRef_as_needed P) b
     | x         => x
(*
  let val exprec = (* 2011: how do I do this? *)
    fn (rbr as (Ref br)) =>
        if ref_isDefn br andalso (P br)
	   then exprec (ref_VAL br) 
	else rbr
     | (App b)   => umkApp   (expandRef_as_needed P) b
     | (Bind b)  => umkBind2 (expandRef_as_needed P) b
     | (Tuple b) => umkTuple (expandRef_as_needed P) b
     | (CnLst b) => umkCnLst (expandRef_as_needed P) b
     | (Proj b)  => umkProj  (expandRef_as_needed P) b
     | (RedTyp b)=> umkRedTyp (expandRef_as_needed P) b
     | x         => x
  
  in share exprec end
 *)

(* ********************************************************************* *)
(* moved from Namespace *)

local   (* substitutions of *closed* terms for Ref's (by timestamp) *)
  fun sub_Ref s = 
    let
      fun sub_rec (Ref br)  = (Mod(assoc (ref_ts br) s) handle Assoc => UMod)
	| sub_rec (Var b)   = mkVar sub_rec b
	| sub_rec (App b)   = mkApp sub_rec b
	| sub_rec (Bind b)  = mkBind2 sub_rec b
	| sub_rec (Tuple b) = mkTuple sub_rec b
	| sub_rec (CnLst b) = mkCnLst sub_rec b
	| sub_rec (Proj b)  = mkProj sub_rec b
	| sub_rec (RedTyp b)= mkRedTyp sub_rec b
	| sub_rec (LabVT b) = mkLabVT sub_rec b
	| sub_rec _         = UMod
    in sub_rec
    end
in (* needed here and in discharge.sml for Cut *)
  fun sub_Ref_pr s = share2f (sub_Ref s)  (** type cnstr modif **)
  (* ************* = share2 (sub_Ref s,sub_Ref s) ************* *)
  fun subRef s = share (sub_Ref s)
  fun subRef_pr s = share (sub_Ref_pr s)
end;

(** ex-variable substitution **)

(* Apply a substitution to a construction *)
(* NOTE: we don't lift, so a substitution can have NO free
 * object-language variables.  This is enforced by reunion *)

fun sub ([]:substitution) = (fn (c:cnstr) => c) (* I *) 
  | sub s  =  
    let
      fun sub_rec (Var(b as (n,_))) =
	   (Mod(assoc n s) handle _ => mkVar sub_rec b)
	| sub_rec (App b)   =  mkApp sub_rec b
(* 
	| sub_rec (try as Bind(b as ((Thry,_),_,_,_))) =
	  ((*if (!theory_debug)
	       then (prs"\n##thry_debug:sub in ";legoprint try)
	   else ()*)
	   thry_debug "\n##thry_debug:sub in " legoprint try;
	   mkBind2 sub_rec b)
 *)
	| sub_rec (Bind b)  =  mkBind2 sub_rec b
	| sub_rec (Tuple b) =  mkTuple sub_rec b
	| sub_rec (CnLst b) =  mkCnLst sub_rec b
	| sub_rec (Proj b)  =  mkProj sub_rec b
	| sub_rec (RedTyp b)=  mkRedTyp sub_rec b
	| sub_rec (LabVT b) =  mkLabVT sub_rec b
	| sub_rec _         =  UMod
    in 
       share sub_rec 
    end

fun sub_pr sbst (VT as (V,T)) = (* LegoUtils.pair_apply (sub sbst) VT *)
  let val sub_fun = sub sbst in (sub_fun V,sub_fun T) end;


(* compose a binding with a substitution *)
(** Warning: depends on 'sub' searching from head to tail
 ** because composite may have multiple bindings for a variable *)

fun compose sub (b:substitution) (s:substitution) : substitution = 
  case b
    of [(m,_)] => (List.map (fn (n,c) => (n,sub b c)) s) @ b
     | _ => bug"compose";


(* optimise the common cases: when sub is sub or subRef, b a single assignment *)

fun sub1 (m,t) = 
    let
      fun sub_rec (Var(b as (n,_))) = if n=m then Mod(t) else mkVar sub_rec b
	| sub_rec (App b)   =  mkApp sub_rec b
	| sub_rec (Bind b)  =  mkBind2 sub_rec b
	| sub_rec (Tuple b) =  mkTuple sub_rec b
	| sub_rec (CnLst b) =  mkCnLst sub_rec b
	| sub_rec (Proj b)  =  mkProj sub_rec b
	| sub_rec (RedTyp b)=  mkRedTyp sub_rec b
	| sub_rec (LabVT b) =  mkLabVT sub_rec b
	| sub_rec _         =  UMod
    in 
       share sub_rec 
    end

local   (* substitutions of *closed* terms for Ref's (by timestamp) *)
  fun sub1_Ref (m,t) = 
    let
      fun sub_rec (Ref br)  = if (ref_ts br) = m then Mod(t) else UMod
	| sub_rec (Var b)   = mkVar sub_rec b
	| sub_rec (App b)   = mkApp sub_rec b
	| sub_rec (Bind b)  = mkBind2 sub_rec b
	| sub_rec (Tuple b) = mkTuple sub_rec b
	| sub_rec (CnLst b) = mkCnLst sub_rec b
	| sub_rec (Proj b)  = mkProj sub_rec b
	| sub_rec (RedTyp b)= mkRedTyp sub_rec b
	| sub_rec (LabVT b) = mkLabVT sub_rec b
	| sub_rec _         = UMod
    in sub_rec
    end
in (* needed here and in discharge.sml for Cut *)
  fun sub1_Ref_pr s = share2f (sub1_Ref s)  (** type cnstr modif **)
  (* ************* = share2 (sub_Ref s,sub_Ref s) ************* *)
  fun sub1Ref s = share (sub1_Ref s)
  fun sub1Ref_pr s = share (sub1_Ref_pr s)
end;

fun composeSub1 (b as (m,t):assignment) s = (List.map (fn (n,c) => (n,sub1 b c)) s) @ [b]

fun composeSubRef1 (b as (m,t):assignment) s = (List.map (fn (n,c) => (n,sub1Ref b c)) s) @ [b]

end; (* local *)

end; (* struct *)
