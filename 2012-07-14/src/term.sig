(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature TERM = 
sig

val theory_debug : bool ref

datatype visSort = Def | Hid | VBot | Vis
datatype bindSort = Lda | Let | Pi | Sig | Thry

type bindVisSort = bindSort * visSort

val LetDef  : bindVisSort
val SigVBot : bindVisSort

datatype projSort = Fst | Labl of string | Snd
datatype prntVisSort = NoShow | ShowExp | ShowForce | ShowNorm
datatype LocGlob = Global | Local
datatype Frz = Froz | UnFroz

val isFrozen : Frz -> bool
val isUnFrozen : Frz -> bool

val mkFrz : bool -> Frz

val prFrz : Frz -> string

val isLocal : LocGlob -> bool
val isGlobal : LocGlob -> bool

val mkLG : bool -> LocGlob

val loc2glob : LocGlob -> LocGlob

val prLocGlob : LocGlob -> string

val prProjSym : projSort -> string

val prVisSym : visSort -> string
val prHidSym : visSort -> string
val prBndSym : visSort -> string

val prVis : visSort -> prntVisSort

type frzLocGlob = Frz * LocGlob

val UnfGlb : frzLocGlob
val UnfLoc : frzLocGlob
val FrzGlb : frzLocGlob

datatype Kind
  = Bnd
  | Config of string * (string * string * string) (* 2011 *)
  | GenTag of string list
  | LabelTag of string list * string
  | Mrk of string * string list * Utils.Timing.time * Utils.Timing.timer
  | Red
  | StThry of string

datatype label = Name of string | RedPr | StrongCast | WeakCast
datatype instrs = iNrml

type 'a exvar = int 
val exvar_index : 'a exvar -> int

val exvar_toString : 'a exvar -> string 

type 'a binder_data = bindVisSort * string * 'a * 'a

type binding_data 
(* = {bd:cnstr binder_data, deps:string list, frz:Frz ref, kind:Kind, param:LocGlob, ts:int} *)

datatype binding = Bd of binding_data

datatype cnstr
  = App of (cnstr * cnstr list) * prntVisSort list
  | Bind of bindVisSort * string * cnstr * cnstr
  | Bot
  | Case of cnstr * cnstr
  | CnLst of cnstr list
  | LabVT of label * cnstr * cnstr
  | Proj of projSort * cnstr
  | Prop
  | RedTyp of instrs * cnstr
  | Ref of binding
  | Rel of int
  | Theory
  | Tuple of cnstr * cnstr list
  | Type of Universes.node
  | Var of int * cnstr

datatype Prefix = Prefix of bindSort * visSort * Frz * LocGlob * string list

val pfxNullDeps : Prefix -> Prefix
val pfxUnfGlb 	: string list -> Prefix -> Prefix
val pfxUnfGlb0 	: Prefix -> Prefix

val pfxLdaL : Prefix
val pfxLdaG : Prefix

val pfxIsPi : Prefix -> bool 

val mkNewBnd : Kind -> Prefix -> string  -> cnstr * cnstr -> binding

val init_binding : unit -> binding

val isKind : cnstr -> bool

val isRef : cnstr -> bool
val isLda : cnstr -> bool
val isPi : cnstr -> bool
val isSig : cnstr -> bool
val isThry : cnstr -> bool
val isTuple : cnstr -> bool

val cnstr_size : cnstr -> int

(* val ref_body : binding -> binding_data *)
val ref_ts : binding -> int
val ref_frz : binding -> Frz ref
val ref_param : binding -> LocGlob
val ref_deps : binding -> string list
val ref_kind : binding -> Kind
val ref_isRed : binding -> bool
val ref_isBnd : binding -> bool
val ref_isMrk : binding -> bool
val ref_isConfig : binding -> bool
val ref_isInfix : binding -> bool
val ref_bd : binding -> cnstr binder_data
val ref_red : binding -> cnstr
val ref_bind : binding -> bindSort
val ref_vis : binding -> visSort
val ref_nam : binding -> string
val ref_mrk : binding -> string
val ref_imports : binding -> string list
val ref_filtim : binding -> Utils.Timing.time
val ref_marktim : binding -> Utils.Timing.timer
val ref_config : binding -> string * (string * string * string)
val ref_infix : binding -> string * string * string
val ref_stThry : binding -> string option
val ref_vt : binding -> cnstr * cnstr
val ref_isLocal : binding -> bool
val ref_isGlobal : binding -> bool
val ref_isFrozen : binding -> bool
val ref_isUnFrozen : binding -> bool
val ref_isDefn : binding -> bool
val ref_isDefnNow : binding -> bool
val ref_isDecl : binding -> bool
val ref_VAL : binding -> cnstr
val ref_TYP : binding -> cnstr
val ref_val : binding -> cnstr
val ref_typ : binding -> cnstr

val ref_updat_vt : binding -> cnstr * cnstr -> binding
val ref_updat_vtdeps : binding -> cnstr * cnstr -> string list -> binding

val ref_promote_to_def : binding -> string -> cnstr * cnstr -> binding

val sameRef : binding -> binding -> bool
val depRef : binding -> binding -> bool
val sameNam : binding -> string -> bool
val mtnNam : string -> binding -> bool
val sameMrk : string -> binding -> bool

val var_occur : cnstr -> bool
val varn_occur : int -> cnstr -> bool
val free_occur : cnstr -> bool
val depends : binding -> cnstr -> bool
val mentions : string -> cnstr -> bool

val pure : cnstr -> bool
val semi_pure : cnstr -> bool
val mv_occur : int -> cnstr -> bool
val Pure : string -> cnstr -> bool

val Type0 : cnstr
val Type1 : cnstr
val Type2 : cnstr
val mkTyp : Universes.node -> cnstr

val mkType0 : cnstr

      type 'a modif = 'a Utils.Modif.modif

val mkAppBod 
  : ('a -> 'a modif) -> ('a * 'a list) * 'b -> (('a * 'a list) * 'b) modif
val mkTupleBod : ('a -> 'a modif) -> 'a * 'a list -> ('a * 'a list) modif
val mkCnLstBod : ('a -> 'a modif) -> 'a list -> 'a list modif
val mkProjBod : ('a -> 'b modif) -> 'c * 'a -> ('c * 'b) modif
val mkRedTypBod : ('a -> 'b modif) -> 'c * 'a -> ('c * 'b) modif
val mkLabVTBod : ('a -> 'a modif) -> 'b * 'a * 'a -> ('b * 'a * 'a) modif
val mkCaseBod : ('a -> 'a modif) -> 'a * 'a -> ('a * 'a) modif
val mkBindBod 
  : (int -> 'a -> 'a modif)
    -> int -> 'a binder_data -> ('a binder_data) modif
val mkBindBod2 
  : ('a -> 'a modif) -> 'b * 'c * 'a * 'a -> ('b * 'c * 'a * 'a) modif
val mkVar : ('a -> cnstr modif) -> int * 'a -> cnstr modif
val umkVar : ('a -> cnstr) -> int * 'a -> cnstr
val MkApp : (cnstr * cnstr list) * prntVisSort list -> cnstr
val mkApp 
  : (cnstr -> cnstr modif)
    -> (cnstr * cnstr list) * prntVisSort list -> cnstr modif
val umkApp : ('a -> cnstr) -> ('a * 'a list) * prntVisSort list -> cnstr
val MkTuple : cnstr * cnstr list -> cnstr
val mkTuple : (cnstr -> cnstr modif) -> cnstr * cnstr list -> cnstr modif
val umkTuple : ('a -> cnstr) -> 'a * 'a list -> cnstr
val MkCnLst : cnstr list -> cnstr
val mkCnLst : (cnstr -> cnstr modif) -> cnstr list -> cnstr modif
val umkCnLst : ('a -> cnstr) -> 'a list -> cnstr
val MkProj : projSort * cnstr -> cnstr
val mkProj : ('a -> cnstr modif) -> projSort * 'a -> cnstr modif
val umkProj : ('a -> cnstr) -> projSort * 'a -> cnstr
val MkRedTyp : instrs * cnstr -> cnstr
val mkRedTyp : ('a -> cnstr modif) -> instrs * 'a -> cnstr modif
val umkRedTyp : ('a -> cnstr) -> instrs * 'a -> cnstr
val MkLabVT : label * cnstr * cnstr -> cnstr
val mkLabVT 
  : (cnstr -> cnstr modif) -> label * cnstr * cnstr -> cnstr modif
val umkLabVT : ('a -> cnstr) -> label * 'a * 'a -> cnstr
val MkCase : cnstr * cnstr -> cnstr
val mkCase : (cnstr -> cnstr modif) -> cnstr * cnstr -> cnstr modif
val umkCase : ('a -> cnstr) -> 'a * 'a -> cnstr

exception Lift
val lift_unshared : int -> cnstr -> cnstr modif
val lift : int -> cnstr -> cnstr

val MkBind : bindVisSort * string * cnstr * cnstr -> cnstr
val mkBind 
  : (int -> cnstr -> cnstr modif) -> int -> cnstr binder_data -> cnstr modif
val mkBind2 
  : (cnstr -> cnstr modif)
    -> cnstr binder_data -> cnstr modif
val umkBind 
  : (int -> 'a -> cnstr)
    -> int -> 'a binder_data -> cnstr
val umkBind2 
  : ('a -> cnstr) -> 'a binder_data -> cnstr

val MkThry : cnstr list -> cnstr

(* 
 *)

val BotVT : cnstr * cnstr
val PT_VT : cnstr * cnstr

    val failSORT   : string -> 'a (* *** belongs somewhere *** *)

val thry_debug : string -> ('a -> unit) -> 'a -> unit

(* ********************************************************************* * 
(* 2011: moved from subst *)
val subst1	 : cnstr -> cnstr -> cnstr
val subst1closed : cnstr -> cnstr -> cnstr

(* 2011: moved from Unif *)
type assignment (* = int * cnstr *)
type substitution (* = assignment list *)

val emptySub : substitution

(* 2011: moved from Namespace *)
(* for discharge and for implementation of Cut: refactor!!! *)
val sub_Ref_pr : substitution -> cnstr * cnstr -> (cnstr * cnstr) modif
val subRef     : substitution -> cnstr -> cnstr
val subRef_pr  : substitution -> cnstr * cnstr -> cnstr * cnstr 

 * ********************************************************************* *)

 val tocr : (cnstr -> cnstr) ref (* hack for now *)

end