(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* 
functor Term (structure Universes:UNIVERSES) 
 *)

structure Term 
	: TERM 

 = 

struct 

        type 'a modif = 'a Utils.Modif.modif

	val bug = Utils.Except.bug
	val failwith = Utils.Except.failwith

	val prs = Printing.prs



val theory_debug = ref false;

(* thry debugging equipment: pass the printer in explicitly *)

fun thry_debug msg prntr c = 
    if !theory_debug 
       then (prs msg; prntr c)
    else ()

(* term.sml *)

datatype visSort  = Vis | Hid | Def | VBot
datatype bindSort = Lda | Pi  | Sig | Let | Thry
datatype projSort = Fst | Snd | Labl of string

type bindVisSort = bindSort * visSort

val LetDef = (Let,Def)
val SigVBot = (Sig,VBot)

datatype prntVisSort = ShowNorm | ShowForce | NoShow | ShowExp 

datatype LocGlob = Local | Global

val isLocal = fn Local => true | _ => false
val isGlobal = fn Global => true | _ => false

val mkLG = fn true => Global | false => Local

val prLocGlob = fn Local => "local" | Global => "global"

val loc2glob = fn Local => Global | Global => Local 

datatype Frz = Froz | UnFroz
type frzLocGlob = Frz * LocGlob

val UnfGlb = (UnFroz,Global)
val UnfLoc = (UnFroz,Local)
val FrzGlb = (Froz,Global)

val isFrozen = fn Froz => true | _ => false
val isUnFrozen = fn UnFroz => true | _ => false

val mkFrz = fn true => UnFroz | false => Froz

local 
    val frozen = "frozen"
in 
   val prFrz = fn Froz => frozen | UnFroz => "un"^frozen
end; 

(* from legoformat *)

  val prBndSym =
    fn Vis => ":" | Hid => "|" | Def => "=" | VBot => bug"bindSym"

  val prVisSym =
    fn Vis => ":" | _ => "|" 

  val prHidSym =
    fn Hid => "|" | _ => ":" 

  val prProjSym = fn Fst => ".1" | Snd => ".2" | Labl(s) => "^"^s

datatype Kind =
  Red
| Bnd
| LabelTag of (string list) * string
| GenTag of (string list)
| Mrk of string * (string list) * Utils.Timing.time * Utils.Timing.timer
| Config of string * (string * string * string) (* 2011 *)
| StThry of string

datatype label = Name of string | WeakCast | StrongCast | RedPr
datatype instrs = iNrml (* 1998: never subsequently pursued *)

fun prVis Vis = ShowNorm 
  | prVis Hid = NoShow
  | prVis Def = bug"prVis: Def"
  | prVis VBot = bug"prVis: VBot";

type 'a exvar = int 
val exvar_index = fn n => n

val exvar_toString = fn n => Int.toString n

type 'a binder_data = bindVisSort * string * 'a * 'a

(** Abstract syntax **)
datatype cnstr = Bot
  | Prop
  | Theory                                  (* the type of theories *)
  | Type of Universes.node			    (* universe levels *)
  | Ref of binding			    (* free variable *)
  | Rel of int                              (* bound variable *)
  | App of (cnstr * (cnstr list)) * (prntVisSort list) (* application *)
  | Bind of cnstr binder_data
  | Var of int * cnstr                      (* existential variable *)
  | Tuple of cnstr * (cnstr list)           (* elem of Sig *)
  | Proj of projSort * cnstr
  | LabVT of label * cnstr * cnstr          (* labeled trm:typ pair *)
  | CnLst of cnstr list                     (* for use in Theories *)
  | RedTyp of instrs * cnstr     (* reduce the synthesised type using insts *)
  | Case of cnstr * cnstr        (* case *)

and binding = Bd of binding_data

withtype binding_data = {kind:Kind, ts:int, 
	   	    frz:Frz ref, param:LocGlob, deps:string list,
	   	    bd:cnstr binder_data}

val is_pi   = fn Pi => true | _ => false
val is_lda  = fn Lda => true | _ => false
val is_sig  = fn Sig => true | _ => false
val is_thry = fn Thry => true | _ => false

val isLet = fn Let => true | _ => false

(* can't define this yet! we don't have the printers for debugging *)
(* 
local 

      val legoprint = Pretty.legoprint
      val print_expand = Pretty.print_expand
(*  *)
      fun flre opn = if (!st_debug) then opn() else ()
in 

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
	    if (univ_cmp n1 n2) (* 2011 *)
	      then true
	    else (flre (fn()=> message"**sT_deb f: TypeType"); false)
	| (Prop,Type _) =>
	    if (!LuosMode) then true
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
	 tryUniverses samTrm (c,d)
    end
end;
 *)

(* *** and goal = int * cnstr with term constructor Var of goal *** *)

val isKind = fn Prop => true | Type _ => true | _ => false (* better name: isSort? *)


fun isRef  (Ref b)  = true
  | isRef _ = false

fun isLda  (Bind ((b,_),_,_,_))  = is_lda b
  | isLda _ = false
fun isPi   (Bind ((b,_),_,_,_))  = is_pi b
  | isPi _ = false
fun isSig  (Bind ((b,_),_,_,_))  = is_sig b 
  | isSig _ = false
fun isThry (Bind ((b,_),_,_,_))  = is_thry b
  | isThry _ = false;

fun isTuple (Tuple _) = true
  | isTuple _ = false;


fun cnstr_size c =
  let
    fun bd_size (_,_,l,r) = 1 + (cnstr_size l) + (cnstr_size r)
    fun cs_size cs = List.foldl (fn (c,n) => n + 1 + (cnstr_size c)) 0 cs
  in case c
       of Bot 	  => 1
	| Type(_) => 1
	| Prop 	  => 1
	| Theory  => 1
	| Ref(Bd{bd=bd,...}) => 1
	| Rel(_) 	     => 1
	| App((f,cs),_) => 1+(cnstr_size f)+(cs_size cs)
	| Bind(bd) 	=> 1+(bd_size bd)
	| Var(_,c) 	=> 1+(cnstr_size c)
	| Tuple(T,cs) 	=> 1+(cnstr_size T)+(cs_size cs)
	| CnLst(cs) 	=> 1+(cs_size cs)
	| RedTyp(_,c) 	=> 1+(cnstr_size c)
	| Proj(_,c) 	=> 1+(cnstr_size c)
	| LabVT(_,c,d) 	=> 1+(cnstr_size c)+(cnstr_size d)
	| Case(v,bs) 	=> 1+(cnstr_size c)+(cnstr_size bs)
  end

(* constructors and destructors *)

fun ref_body (Bd b) = b (* 2011: export Match failure behaviour? *)

fun ref_ts br = #ts (ref_body br)
fun ref_frz br = #frz (ref_body br)
fun ref_param br = #param (ref_body br)
fun ref_deps br = #deps (ref_body br)
fun ref_kind br = #kind (ref_body br)
fun ref_isRed br = case ref_kind br
                     of Red => true | _ => false
fun ref_isBnd br = case ref_kind br
                     of Bnd => true | (GenTag _) => true | _ => false
fun ref_isMrk br = case ref_kind br of Mrk _ => true | _ => false
fun ref_isConfig br = case ref_kind br of Config _ => true | _ => false
fun ref_isInfix br = case ref_kind br of Config (x,_) => x="Infix" | _ => false
fun ref_bd br = #bd (ref_body br)
fun ref_red br = if ref_isRed br then #3 (ref_bd br) else bug"ref_red"
fun ref_bind br = #1 (#1 (ref_bd br))
fun ref_vis br = #2 (#1 (ref_bd br))
fun ref_nam br = #2 (ref_bd br)
fun ref_mrk br = case ref_kind br of Mrk (s,_,_,_) => s | _ => bug"ref_mrk"
fun ref_imports br =
  case ref_kind br of Mrk (_,i,_,_) => i | _ => bug"ref_imports"
fun ref_filtim br =
  case ref_kind br of Mrk (_,_,t,_) => t | _ => bug"ref_filtim"
fun ref_marktim br =
  case ref_kind br of Mrk (_,_,_,t) => t | _ => bug"ref_marktim"
fun ref_config br = case ref_kind br of Config x => x | _ => bug"ref_config"
fun ref_infix br = case ref_kind br of Config ("Infix",x) => x | _ => bug"ref_infix"
fun ref_stThry br = case ref_kind br
		      of StThry x => SOME x | _ => NONE
fun ref_vt br = let val (_,_,v,t) = ref_bd br in (v,t) end
fun ref_isLocal br = isLocal (ref_param br) 
fun ref_isGlobal br = isGlobal (ref_param br) 
fun ref_isFrozen br = isFrozen (!(ref_frz br)) 
fun ref_isUnFrozen br = isUnFrozen (!(ref_frz br)) 
fun ref_isDefn br = ref_isBnd br andalso isLet(ref_bind br)
fun ref_isDefnNow br = ref_isDefn br andalso ref_isUnFrozen br (* (!(ref_frz br))=UnFroz *)
fun ref_isDecl br = ref_isBnd br andalso not(isLet(ref_bind br))
fun ref_VAL br = #3 (ref_bd br)
fun ref_TYP br = #4 (ref_bd br)
fun ref_val br = if ref_isDefnNow br then ref_VAL br
		 else Ref br
(* ***** *
fun ref_val br = if ref_isDefn br then #3 (ref_bd br) else bug"ref_val"
 * ***** *)
fun ref_typ br = (if ref_isDefn br then #4 else #3) (ref_bd br)

fun sameRef br br' = ref_ts br = ref_ts br'
fun depRef bref br = sameRef br bref

fun sameNam br nam = ref_nam br = nam
fun mtnNam  nam br = sameNam br nam

fun sameMrk mrk br = ref_isMrk br andalso ref_mrk br = mrk

fun ref_updat_vt (Bd{ts,frz,param,deps,kind,bd=(bv,nam,_,_)}) (v,t) =
      Bd{ts=ts,frz=frz,param=param,deps=deps,kind=kind,bd=(bv,nam,v,t)};
fun ref_updat_vtdeps (Bd{ts,frz,param,kind,bd=(bv,nam,_,_),...}) (v,t) d =
      Bd{ts=ts,frz=frz,param=param,deps=d,kind=kind,bd=(bv,nam,v,t)};

fun ref_promote_to_def (Bd{ts,kind,deps,param,...}) lft (rv,t) = 
    Bd{ts=ts,kind=kind,deps=deps,
	frz=ref UnFroz,param=loc2glob param,bd=(LetDef,lft,rv,t)}

(* construction of compound bodies... *)

local 
      open Utils.Modif
      open Utils.Counting

in 
(* A Type construction function allows sharing storage *)

val Type0 = Type(Universes.mkUcon 0)
val Type1 = Type(Universes.mkUcon 1)
val Type2 = Type(Universes.mkUcon 2)

val mkTyp = Universes.mkNod (fn nod => Type(nod)) Type0 Type1 Type2 
(*  
   fun mkTyp nod = 
    let 
      (Type0,Type1,Type2) = (Type(mkUcon 0),Type(mkUcon 1),Type(mkUcon 2))
    in 
      case nod
	  of Uconst(0) => Type0
	   | Uconst(1) => Type1
	   | Uconst(2) => Type2
	   | _         => Type(nod)
   end;
 *)

fun mkType n = mkTyp(Universes.mkUcon n)
val mkType0  = mkType 0

(* 2011: moved from context.sml *)

datatype Prefix = Prefix of  bindSort * visSort * Frz * LocGlob * string list

val pfxNullDeps = fn Prefix(b,v,f,l,deps) => Prefix(b,v,f,l,[])
fun pfxUnfGlb nams = fn Prefix(b,v,_,_,deps) => Prefix(b,v,UnFroz,Global,deps@nams)
val pfxUnfGlb0 = fn Prefix(b,v,_,_,deps) => Prefix(b,v,UnFroz,Global,deps)

val pfxLdaL = Prefix(Lda,Vis,UnFroz,Local,[])
val pfxLdaG = Prefix(Lda,Vis,UnFroz,Global,[])

val pfxIsPi = fn Prefix(b,_,_,_,_) => is_pi b

local              (* timestamp used for equality of bindings *)
   val ts = ref 0
   fun timestamp() = (ts:= succ (!ts); !ts)
in
   fun mkNewBnd knd (Prefix (b,vis,frz_flg,par_flg,deps)) nam (v,t) =
       (Bd{ts=timestamp(),
        frz=(ref frz_flg),param=par_flg,
	deps=deps,kind=knd,bd=((b,vis),nam,v,t)})
end;

fun init_binding () = 
   mkNewBnd Bnd (Prefix(Pi,Vis,UnFroz,Global,[])) "** Start of Context **" (Prop,Type0) ; 

     (* non-binders have one form *)
fun mkAppBod f (b,vs) =
  case share2 (f,map_share f) b
    of UMod => UMod
     | Mod(b') => Mod(b',vs)
fun mkTupleBod f Tls = share2 (f,map_share f) Tls
val mkCnLstBod = map_share
fun mkProjBod f (s,b) =
  case f b
    of UMod => UMod
     | Mod(b') => Mod(s,b')
fun mkRedTypBod f (s,b) =
  case f b
    of UMod => UMod
     | Mod(b') => Mod(s,b')
fun mkLabVTBod f (n,v,t) =
  case share2f f (v,t)
    of UMod => UMod
     | Mod(v',t') => Mod(n,v',t')
fun mkCaseBod f (v,t) =
  case share2f f (v,t)
    of UMod => UMod
     | Mod(v',t') => Mod(v',t')

     (* binders have two forms *)
fun mkBindBod f k (t,s,b1,b2) =
  case share2 (f k,f (succ k)) (b1,b2)
    of UMod => UMod
     | Mod(b1',b2') => Mod(t,s,b1',b2')
fun mkBindBod2 f (t,s,b1,b2) = 
  case share2f f (b1,b2)
    of UMod => UMod
     | Mod(b1',b2') => Mod(t,s,b1',b2')
; 

(* canonical term constructors *)
fun mkVar f (u,c) = case f c of UMod => UMod | (Mod c') => Mod(Var(u,c'))
fun umkVar f (u,c) = Var(u,f c)
fun MkApp ((c,[]),_)                  = c
  | MkApp ((App((c',cs'),vs'),cs),vs) = MkApp ((c',cs'@cs),(vs'@vs))
  | MkApp x                           = App(x)
fun mkApp f b =
  let val fb = mkAppBod f b
  in  case fb of UMod => UMod | (Mod fb') => Mod(MkApp(fb'))
  end
fun umkApp f ((c,cs),vs) = MkApp ((f c, List.map f cs),vs)

local 
      fun standard cs =  (* unfold all rightmost Tuples *)
        case List.rev cs
	  of (tpl as Tuple(_,ks))::cs => (List.rev cs)@(standard ks)
	   | cs                       => List.rev cs

in 
   fun MkTuple(T,l) =
       case standard l
       	 of []  => bug"MkTuple"
       	  | [l] => l
       	  | ls  => Tuple(T,ls)
end;

fun mkTuple f b = case mkTupleBod f b
		    of UMod => UMod | (Mod b') => Mod(MkTuple b')
fun umkTuple f (c,cs) = MkTuple(f c, List.map f cs)

fun MkCnLst l = CnLst l
fun mkCnLst f b = case mkCnLstBod f b of UMod => UMod | (Mod b') => Mod(MkCnLst b')
fun umkCnLst f ls = MkCnLst (List.map f ls)

fun MkProj b = Proj(b)
fun mkProj f b = case mkProjBod f b
		   of UMod => UMod | (Mod b') => Mod(MkProj b')
fun umkProj f (p,c) = MkProj(p,f c);

fun MkRedTyp b = RedTyp(b)
fun mkRedTyp f b = case mkRedTypBod f b
		     of UMod => UMod | (Mod b') => Mod(MkRedTyp b')
fun umkRedTyp f (p,c) = MkRedTyp(p,f c);

fun MkLabVT b = LabVT b
fun mkLabVT f b = case mkLabVTBod f b
		    of UMod => UMod | (Mod b') => Mod(MkLabVT b')
fun umkLabVT f (n,v,t) = MkLabVT(n,f v,f t)

fun MkCase b = Case b
fun mkCase f b = case mkCaseBod f b
		   of UMod => UMod | (Mod b') => Mod(MkCase b')
fun umkCase f (v,t) = MkCase(f v,f t)

fun MkThry lvts = Bind((Thry,VBot),"",Theory,CnLst lvts)

(* occurrence *)

(* var_occur tests whether object variable Rel(1) occurs
 * free_occur tests for any free obj var occurrence *)
local
  fun vocc f =  
    let fun voccur_rec p =
      fn Rel(p')        => f(p,p')
       | App((c,cs),_)  => (voccur_rec p c) orelse (List.exists (voccur_rec p) cs)
       | Bind(_,_,c,d)  => (voccur_rec (succ p) d) orelse (voccur_rec p c)
       | Tuple(T,l)     => (voccur_rec p T) orelse (List.exists (voccur_rec p) l)
       | CnLst(l)       => List.exists (voccur_rec p) l
       | Proj(_,c)      => voccur_rec p c
       | RedTyp(_,c)    => voccur_rec p c
       | LabVT(_,v,t)   => (voccur_rec p v) orelse (voccur_rec p t)
       | Case(v,bs)     => (voccur_rec p v) orelse (voccur_rec p bs)
       | _              => false
    in voccur_rec
    end
in

  val var_occur = vocc (op =) 1
  fun varn_occur n = vocc (op =) n
  val free_occur = vocc (op <) 0

end;

local

  fun poccur f =  
    let fun poccrec (Ref(br))       = f br
          | poccrec (App((c,cs),_)) = (poccrec c) orelse (List.exists poccrec cs)
          | poccrec (Bind(_,_,c,d)) = (poccrec d) orelse (poccrec c)
          | poccrec (Tuple(T,l))    = (poccrec T) orelse (List.exists poccrec l) 
          | poccrec (CnLst l)       = List.exists poccrec l
          | poccrec (Proj(_,c))     = poccrec c
          | poccrec (RedTyp(_,c))   = poccrec c
          | poccrec (LabVT(_,v,t))  = poccrec v orelse poccrec t
          | poccrec (Case(v,bs))    = poccrec v orelse poccrec bs
          | poccrec (Var(_,c))      = poccrec c
          | poccrec _               = false
     in poccrec end

in

  fun depends bref = poccur (depRef bref)
  fun mentions nam = poccur (mtnNam nam)

end

(** existential variables: occurrence **)

(* pure c is true if c has no ex-variables  *)

(* semi_pure c is true if c has no ex-vars  * 
 * unresolved from argument synthesis, i.e. * 
 * generated by Concrete.parser_var_pack... *)

(* mv_occur n c is true if Var(n,_) occurs in c *)

local 
  fun occ f = 
    let val rec occ_rec =
      fn Var(x,_) => f (exvar_index x)
       | App((c,cs),vs) => (occ_rec c) andalso (List.all occ_rec cs)
       | Bind(_,_,c,d) => (occ_rec c) andalso (occ_rec d)
       | Tuple(T,ls)   => (occ_rec T) andalso (List.all occ_rec ls)  
       | CnLst(ls)     => List.all occ_rec ls
       | Proj(_,c)     => occ_rec c
       | RedTyp(_,c)   => occ_rec c
       | LabVT(_,v,_)  => (occ_rec v)
       | _             => true
    in occ_rec end
in 
  val pure = occ (fn m => false)
  val semi_pure = occ (fn m => m >= 0)
  fun mv_occur n M = not (occ (fn m => n<>m) M) (* mv_occur n = neg (occ (fn m => n<>m)) *)
end;

fun Pure nam c = (* 2011: moved here from Unif, and then Machine *) 
    if (pure c) then true
    else failwith("attempt to bind "^nam^" to impure term");

(* lifting to avoid capture *)
exception Lift
(** WARNING: This function doesn't use the canonical constructors below **)
fun lift_unshared n =
  if n=0 then (fn _ => UMod)
  else
    let fun lft_rec k (Rel m)  = if m<k then UMod
				  else if (m+n)>0 then  Mod(Rel(m+n))
				       else raise Lift
	  | lft_rec k (App b)   = mkApp (lft_rec k) b
	  | lft_rec k (Bind b)  = mkBind lft_rec k b
	  | lft_rec k (Tuple b) = mkTuple (lft_rec k) b
	  | lft_rec k (CnLst b) = mkCnLst (lft_rec k) b
	  | lft_rec k (Proj b)  = mkProj (lft_rec k) b
	  | lft_rec k (RedTyp b)= mkRedTyp (lft_rec k) b
	  | lft_rec k (LabVT b) = mkLabVT (lft_rec k) b
	  | lft_rec k (Case b)  = mkCase (lft_rec k) b
	  | lft_rec k _         = UMod
    in lft_rec 1
    end
and lift n = share (lift_unshared n)

and MkBind (d as ((Let,_),_,_,b)) = if var_occur b then Bind(d)
				    else lift (~1) b
  | MkBind b                      = Bind(b)
and mkBind f k b =
  let val fb = mkBindBod f k b
  in  case fb of UMod => UMod | (Mod b') => Mod(MkBind b')
  end
and mkBind2 f b =
  let val fb = mkBindBod2 f b
  in  case fb of UMod => UMod | (Mod b') => Mod(MkBind b')
  end
;

fun umkBind f k (t,s,b1,b2) = MkBind((t,s,f k b1,f (succ k) b2))
fun umkBind2 f (t,s,b1,b2) = MkBind((t,s,f b1,f b2));

end; (* of local open Utils *)

(* misc *)
  val BotVT = (Bot,Bot)

  val PT_VT = (Prop,Type0) 

  fun failSORT msg = failwith("Only a Prop or a Type can be "^msg)

(* 2011: reinstated Conor's hack *)

  val tocr = ref (fn (c:cnstr) => c) (* set to toc function *)

  val truePropProof = Bind((Lda,Hid),"P",Prop,
			Bind((Lda,Vis),"p",Rel 1,Rel 1))


end; (* of FunTerm *)

(*
structure Term = Term (structure Universes=Universes);
 *)

