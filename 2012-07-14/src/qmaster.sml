(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

functor FunQuarterMaster
	(structure Term:TERM
	 structure Concrete:CONCRETE
	 structure Namespace:NAMESPACE
	 structure Engine:CONSTRUCTIVEENGINE
	 structure Pretty:PRETTY
	 sharing 
	 	 type Term.cnstr
		    = Concrete.cnstr
		    = Namespace.cnstr
		    = Engine.cnstr
		    = Pretty.cnstr
	 and	 type Term.binding
		    = Namespace.binding
		    = Pretty.binding
	 and	 type Concrete.context
		    = Namespace.context
		    = Engine.context
	 and	 type Concrete.substitution
		    = Namespace.substitution
		    = Engine.substitution
	 and	 type Concrete.cnstr_c
		    = Engine.cnstr_c
	 and	 type Term.Prefix
		    = Concrete.Prefix
	 and	 type Term.Frz
		    = Namespace.Frz
	 and	 type Term.LocGlob
		    = Namespace.LocGlob
	 )
(* *** *
structure QuarterMaster
 * *** *)
	: QUARTERMASTER 

 = 

struct
local

	val TERM = "TERM" 
	val EMPTYTAG = "EMPTYTAG"
	val EMPTYSTRING = "EMPTYSTRING"

	val failwith = Utils.Except.failwith
	val isNullString = Utils.StringUtil.isNullString 

	open Term 

  (* open Concrete *)
  (* open Namespace *)

  exception quartermaster

  val Suppliers = ref ([] :
                       ((Concrete.cnstr_c list) -> (Concrete.cnstr_c * bool)) list)
  fun Supply tag =
      let fun s2 [] = raise quartermaster
            | s2 (h::t) = ((h tag) handle quartermaster => s2 t)
      in  s2 (!Suppliers)
      end

  fun labelTagName [] = EMPTYTAG
    | labelTagName [""] = EMPTYSTRING
    | labelTagName [s] = s
    | labelTagName (h::t) = h^"_"^(labelTagName t)

(* 2011 version *)
  fun magicTagElem s = let
		          val nam = Concrete.getRefNam s
      		       in 
		          if isNullString nam then EMPTYSTRING
			  else nam 
		       end handle Concrete.getConcrete => TERM; 
      		      
  fun magicTagName []  = "EMPTYTAG"
    | magicTagName [s] = magicTagElem s 
    | magicTagName (h::t) = let
			       val s = Concrete.getRefNam h 
				      	handle Concrete.getConcrete => TERM
      		   	    in 
			       s^"_"^(magicTagName t)
			    end;

(* 1998 version *
  fun magicTagName [] = "EMPTYTAG"
    | magicTagName [Concrete.Ref_c ""] = "EMPTYSTRING"
    | magicTagName [Concrete.Ref_c s] = s
    | magicTagName [_] = "TERM"
    | magicTagName ((Concrete.Ref_c s)::t) = s^"_"^(magicTagName t)
    | magicTagName (_::t) = "TERM_"^(magicTagName t)
 *)

  val SLtoCL = List.map Concrete.mkRef_c

(* 2011 version *)
  fun CLtoSLo cts = SOME(List.map (Concrete.getRefNam) cts) 
      handle Concrete.getConcrete => NONE 

(* 1998 version *
  fun CLtoSLo ((Concrete.Ref_c s)::t) =
     (case (CLtoSLo t)
        of (SOME t') => SOME (s::t')
         | _ => NONE)
    | CLtoSLo [] = SOME []
    | CLtoSLo _ = NONE
 *)

  fun doMake tag = 
      let val stag = CLtoSLo tag
          val (term,store) = Supply tag
              handle quartermaster => failwith "No supplier!"
          val VT = Engine.fEval term
      in  case stag of NONE => term | SOME ss =>
          if   (Namespace.activeProofState ()) orelse (not store)
          then term
          else let 
	         val nom =  Namespace.mkNameGbl (magicTagName tag)
	         val _ = Namespace.addGenGbl ss (UnFroz) (Global) [] nom VT 
               in  Concrete.mkRef_c nom
               end
      end

in

  type cnstr_c = Concrete.cnstr_c

  type binder_c = Concrete.binder_c 

  val SLtoCL = SLtoCL
  val CLtoSLo = CLtoSLo

  exception quartermaster = quartermaster

  fun Label tag "" = Label tag (labelTagName tag)
    | Label tag name =
      ( ( (Engine.fEvalNam name);
          (Namespace.addLabel (tag,name));
          () )
        handle _ => failwith ("Could not label "^name) )

  fun Generate_ tag (Prefix(Let,Def,frz_flg,par_flg,deps),[nom],c) =
      let
	 fun doGenTag tag = 
     	     (case Namespace.spotLabel tag
             	of SOME _ => ()
         	 | NONE	  => let 
	           	     	 val _ = Namespace.addGenGbl tag frz_flg par_flg
                                        deps nom (Engine.fEval c)
                 		 val B = Namespace.topNamespace()
                 		 val V = (ref_val B)
		 		 val T = (ref_typ B)
               		     in  Pretty.prnt_defn nom V T (* *** tests interactive () *** *)
               		     end)

      in
		Namespace.NSPWrapper doGenTag tag
      end
    | Generate_ tag _ = ((doMake (SLtoCL tag));())

  fun GenerateProp tag = Generate_ tag (Prefix(Let,VBot,UnFroz,Global,[]),[],Concrete.Prop_c)

  fun GenerateDefn tag nam v_c = Generate_ tag (Prefix(Let,Def,UnFroz,Global,[]),[nam],v_c)

  fun Generate tag bnd = Generate_ tag (Concrete.unBind bnd)

  fun Make tt =
     ((case CLtoSLo tt
         of SOME tag => (case Namespace.spotLabel tag of SOME (x,_) => Engine.unEval x
                            | _ => raise Match)
          | _ => raise Match)
      handle Match => doMake tt)

  fun Register _ = failwith "Register not done yet"
end (* local *)
end; (* struct *)

