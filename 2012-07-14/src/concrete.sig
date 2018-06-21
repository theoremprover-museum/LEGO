local 

in

  signature CONCRETE =
    sig

	type cnstr 
	type context 
	type substitution 

	type Prefix
	type instrs
	type projSort
	type bindSort
	type visSort
	type prntVisSort
	type LocGlob
	type Frz

	type cnstr_c (* 2011: datatype is "abstract" now *)

(* ************* *)
  type binder_c
  type ctxt_c
(* ************* *)

(* ********** *)
   val unBind : binder_c -> Prefix * string list * cnstr_c
   val unCtxt : ctxt_c -> binder_c list

   val mkBind : Prefix * string list * cnstr_c -> binder_c
   val mkCtxt : binder_c list -> ctxt_c

   val nil_c  : ctxt_c
   val cons_c : binder_c -> ctxt_c -> ctxt_c

(* ********** *)

        val App_c    : prntVisSort * cnstr_c * cnstr_c -> cnstr_c 
      	val Bind_c   : binder_c * cnstr_c -> cnstr_c 
      	val Cast_c   : cnstr_c * cnstr_c -> cnstr_c 
      	val Case_c   : cnstr_c * (ctxt_c * cnstr_c * cnstr_c) list -> cnstr_c 
	val Ctxt_c   : ctxt_c * cnstr_c -> cnstr_c 
      	val Red_c    : ctxt_c * ((cnstr_c*cnstr_c) list) -> cnstr_c 

        val Prop_c   : cnstr_c
        val Theory_c : cnstr_c
        val Bot_c    : cnstr_c

        val Var_c    : int -> cnstr_c
        val NewVar_c : cnstr_c

        val TypeOf_c : cnstr_c -> cnstr_c
	val Normal_c : cnstr_c -> cnstr_c
      	val Hnf_c    : int * cnstr_c -> cnstr_c
      	val Dnf_c    : cnstr_c -> cnstr_c

	val Gen_c    : cnstr_c * string -> cnstr_c

	val TYPE_c   : cnstr_c 

(* ************* *
      datatype cnstr_c = Bot_c
      | Prop_c
      | Theory_c
      | Type_c of string
      | TypeAbs_c of int
      | Ref_c  of string
      | App_c  of prntVisSort * cnstr_c * cnstr_c
      | Bind_c of binder_c * cnstr_c
      | Tuple_c of (cnstr_c list) * cnstr_c
      | Proj_c of projSort * cnstr_c
      | Ctxt_c of ctxt_c * cnstr_c
      | Cast_c of cnstr_c * cnstr_c
      | wCast_c of cnstr_c * cnstr
      | Case_c of cnstr_c * (ctxt_c * cnstr_c * cnstr_c) list
      | Red_c of ctxt_c * ((cnstr_c*cnstr_c) list)
      | Var_c  of int  (* metavars for use in refinements *)
      | NewVar_c       (* make a new metavar *)
      | Normal_c of cnstr_c
      | Hnf_c of int * cnstr_c
      | Dnf_c of cnstr_c
      | RedTyp_c of instrs * cnstr_c
      | TypeOf_c of cnstr_c
      | Gen_c of cnstr_c * string
 * ************* *)

(* *** constructors used by lego.grm.sml: make this full-fledged and hide cnstr_c? *** *)

      val mkRef_c : string -> cnstr_c

      val mkBind_c   : (Prefix * string list * cnstr_c) * cnstr_c -> cnstr_c 

      val mkApp_c    : (cnstr_c * cnstr_c) -> cnstr_c
      val mkAppForce_c   : (cnstr_c * cnstr_c) -> cnstr_c
      val mkAppNoShow_c   : (cnstr_c * cnstr_c) -> cnstr_c
      val mkLift_c   : cnstr_c -> cnstr_c
      val mkLiftForce_c  : cnstr_c -> cnstr_c

      val mkInfixApp_c : (string * cnstr_c * cnstr_c) -> cnstr_c	(* added 2011 *)

(* changed again 2011-11-29 *
      val MkDecl : bindSort -> LocGlob -> 
      	  (visSort * (string list) * cnstr_c) * (string list) -> binder_c 

      val MkDefn : Frz * LocGlob -> 
      	  ((string list) * cnstr_c) * (string list) -> binder_c 
 * ************************ *)

      val mkVis : visSort
      val mkHid : visSort
      val mkQM  : visSort

      val mkLLda : (visSort * (string list) * cnstr_c) * (string list) -> binder_c 
      val mkGLda : (visSort * (string list) * cnstr_c) * (string list) -> binder_c 
      val mkLPi  : (visSort * (string list) * cnstr_c) * (string list) -> binder_c 
      val mkLSig : (visSort * (string list) * cnstr_c) * (string list) -> binder_c 

      val mkLDefn : ((string list) * cnstr_c) * (string list) -> binder_c 
      val mkGDefn : ((string list) * cnstr_c) * (string list) -> binder_c 
      val mkFDefn : ((string list) * cnstr_c) * (string list) -> binder_c 

      val mkPiExp_c  : visSort -> LocGlob -> string list -> cnstr_c -> cnstr_c -> cnstr_c      
      val mkLdaExp_c : visSort -> LocGlob -> string list -> cnstr_c -> cnstr_c -> cnstr_c

      val mkArr_c    : (cnstr_c * cnstr_c) -> cnstr_c
      val mkLda_c    : (cnstr_c * cnstr_c) -> cnstr_c
      val mkSig_c    : (cnstr_c * cnstr_c) -> cnstr_c
      val mkFst_c    :  cnstr_c -> cnstr_c
      val mkSnd_c    :  cnstr_c -> cnstr_c
      val mkTuple_c  : (cnstr_c list) * cnstr_c -> cnstr_c
      val mkLabProj_c : (string * cnstr_c) -> cnstr_c

      val mkRed_c    : ctxt_c * ((cnstr_c*cnstr_c) list) 
      	  	        -> cnstr_c

      val mkRed0_c    : ((cnstr_c*cnstr_c) list) -> cnstr_c

      val mkRedTyp_c : cnstr_c -> cnstr_c

      exception TypeNamError of cnstr_c (* odd: tms was wrong? in lego-grm *)

      val mkType_c    : unit -> cnstr_c
      val mkTypeAbs_c : int -> cnstr_c
      val mkTypeNam_c : cnstr_c -> cnstr_c (* here? see lego-grm *)

(* ******************************************* *)


(* *** indicators used by ind_relations etc. *** *)

      val isBot  : cnstr_c -> bool (* only for the Qrepl setup in tactics *)
      val isRef  : cnstr_c -> bool
      val isHead : cnstr_c -> bool
      val isTYPE : cnstr_c -> bool (* is Type_c("") *)

(* *** destructors used by ind_relations etc. *** *)

      exception getConcrete (* potentially raised by each of these *)

      val getRefNam  : cnstr_c -> string 

      val getAppData : cnstr_c -> prntVisSort * cnstr_c * cnstr_c

      val getBinder  : cnstr_c -> (Prefix * string list * cnstr_c) * cnstr_c

      val getEndType : cnstr_c -> cnstr_c

      val getEnd     : cnstr_c -> string

      val subForType : string -> cnstr_c -> cnstr_c

      exception errConcrete (* potentially raised by each of these *)

      val contains  : string list -> cnstr_c -> bool 

      val subForNam : (string * string) -> cnstr_c -> cnstr_c 
      val subForRef : (string * cnstr_c) -> cnstr_c -> cnstr_c 

      val unEval_  : context ->                                      
   	  	     cnstr -> cnstr_c                                

      val fEval_   : context ->                                      
    	  	     (int -> cnstr) ->                               
		     (cnstr -> cnstr) ->                              
		     cnstr_c -> (cnstr * cnstr) * substitution       

    end (* sig *)

end; (* local *)

local

in 

  signature CONSTRUCTIVEENGINE =
    sig

	type cnstr 
	type context 
	type substitution 
	type cnstr_c 

(* ***************************************************************** *)
(* *** the constructive engine and friends: these need Namespace *** *)

      val mkRef_c : string -> cnstr_c

      val unEval   : cnstr -> cnstr_c

      val fEvalCxt : context -> 
      	  	     cnstr_c -> cnstr * cnstr

      val fEval    : cnstr_c -> cnstr * cnstr

      val fEvalVal : cnstr_c -> cnstr 
      val fEvalTyp : cnstr_c -> cnstr 

      val fEvalNam : string  -> cnstr * cnstr

      val RefVal_s : string  -> cnstr 
      val RefTyp_s : string  -> cnstr 

(*    val parser_var_pack : unit -> cnstr -> cnstr *)

      val EvalRefine_ : (int -> cnstr) -> 
	  	        (cnstr -> cnstr) -> 
		 	 cnstr_c -> (cnstr * cnstr) * substitution

(* *** added 2011, refactored uses of EvalRefine ******************* *)

      val EvalRefine  : (cnstr -> cnstr) -> 
			 cnstr_c -> (cnstr * cnstr) * substitution

      val EvalRefine0 :  cnstr_c -> (cnstr * cnstr) 

(* ***************************************************************** *)

    end (* sig *)

end; (* local *)

