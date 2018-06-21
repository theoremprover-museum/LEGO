(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* *************************************************************************** *)
(* context.sml:   factorise out the context manipulations before namespace.sml *)
(* *************************************************************************** *)

functor FunContext (structure Term:TERM
		    )
(* *************************************************************************** *
structure Context 
 * *************************************************************************** *)
 : 	  CONTEXT 
 =

struct
	
local 

      val failwith = Utils.Except.failwith 

      open Term

in

	type cnstr = Term.cnstr
	type binding = Term.binding 
	type context = binding list

(* *)

   fun mkCxt brs : binding list = brs : context

   fun unCxt cxt : context = cxt : binding list

   val emptyCxt = [] : context

   val isEmptyCxt = fn [] => true | _ => false 

   fun addBndCxt bnd cxt = bnd :: cxt : context

   fun popCxt cxt = case cxt
       	      	      of br :: brs => (br,brs)
		       |    [] 	   => failwith"Context: Empty! no top"; 

   fun topCxt cxt = let val (br,_) = popCxt cxt in br end 

   fun takeCxt n cxt = unCxt (List.take(cxt,n))

(* now: initialise the context *)

   fun init_context () = addBndCxt (init_binding()) emptyCxt : context

(* expansions of the context *)
   fun mkSpecialCxtBnd knd vt = mkNewBnd knd (Prefix(Sig,VBot,UnFroz,Global,[])) "" vt 

   fun mkSpecialCxtBnd0 knd = mkSpecialCxtBnd knd BotVT

(* specials, for all the extras that the kitchen sink acquired *)

   fun mkLabelBnd tn = mkSpecialCxtBnd0 (LabelTag tn)

   fun addLabelCxt tn cxt = addBndCxt (mkLabelBnd tn) cxt

   fun mkThryBnd nam = mkSpecialCxtBnd0 (StThry nam)

   fun addThryCxt nam = addBndCxt (mkThryBnd nam)

   fun mkConfigBnd config = mkSpecialCxtBnd0 (Config config)

   fun addConfigCxt config = addBndCxt (mkConfigBnd config)

   fun mkMarkBnd (m,i,t) = mkSpecialCxtBnd0 (Mrk(m,i,t,Utils.Timing.start_timer()))

   fun addMarkCxt (m,i,t) = addBndCxt (mkMarkBnd (m,i,t))

   val mkReductBnd = mkSpecialCxtBnd Red

   fun addReductCxt VT = addBndCxt (mkReductBnd VT) ;

(* ************************************************************************ *
 * ************************************************************************ *)

(* List.app s for various tasks, e.g. printing: validate length etc. *)

local

   fun do_cxt_dpth_ act n cxt = 
       if n <= 0 then ()
       else 
       	    let
		val len = List.length cxt
      		val real_n = if n>len then len else n (* avoid Subscript exn *)
    	    in
		List.app act (List.rev (List.take (cxt,real_n))) (* here *)	 
    	    end

   fun depth f m = fn b::rest => if f b then m else depth f (m+1) rest
      	      	    |  []     => m
in 

   val do_cxt_dpth = do_cxt_dpth_

   fun do_cxt act cxt = do_cxt_dpth_ act (List.length cxt) cxt

   fun do_cxt_ref br act cxt =
     do_cxt_dpth_ act (depth (depRef br) 0 cxt) cxt

   fun do_cxt_nam nam act cxt =
     do_cxt_dpth_ act (depth (mtnNam nam) 1 cxt) cxt

end;

(* ************************************************************************ *)
(* context search belongs here more appropriately than in Machine/Namespace *)

local

    (* fun findBind nam = fn Bd{bd=(_,n,_,_),...} => n=nam *)

    val findBind = mtnNam 

    fun findCxt  id  = List.find (findBind id)

    fun found (SOME bd) f   _  = f bd
      | found  NONE     _ fail = fail()

    fun return b = b
    
in

  fun searchCxt nam cxt = 
      let 
      	 fun fail() = failwith("search: undefined or out of context: "^nam)
      in 
      	 found (findCxt nam cxt) return fail 
      end 

  fun   Defined nam     = List.exists (findBind nam)

  fun unDefined nam cxt = not (Defined nam cxt)

  fun findLabelCxt tag cxt =
      let fun gotB b = if ref_isBnd b then SOME (Ref b,ref_typ b) else NONE
          fun s2 [] = NONE
            | s2 (b::t) = let val k = ref_kind b
                          in  case k
                                of LabelTag (tag',id) =>
				   if tag=tag'
                                   then found (findCxt id cxt) gotB (fn _ => NONE)
                                   else s2 t
                                 | GenTag tag' => if tag=tag'
                                                  then gotB b
                                                  else s2 t
                                 | _ => s2 t
                          end
      in  s2 cxt
      end

  fun findConfigCxt key fail =
      let
(* 
         fun fc2 [] = fail
           | fc2 ((Bd{kind=Config(a,cfgdata),...})::tail) = (* 2011 *)
                if (a=key) then cfgdata else fc2 tail
           | fc2 (_::tail) = fc2 tail
 *)
         fun fc2 [] = fail
           | fc2 (br::brs) = if ref_isConfig br 
	     	 	     then 
			     	  let
				     val (a,cfgdata) = ref_config br 
				  in if (a=key) then cfgdata else fc2 brs
				  end
			     else fc2 brs
(*                 
         fun fc2 [] = fail
           | fc2 (br::brs) = (let
				 val (a,cfgdata) = ref_config br 
			      in if (a=key) then cfgdata else fc2 brs
			      end) handle _ => fc2 brs
 *)
      in
         fc2 
      end

end;

(* split context when property pred becomes true *)
fun splitCxt pred msg = 
  let
    fun splrec pre (br::brs) = if pred br then (br,pre,brs)
			       	  else splrec (br::pre) brs
      | splrec pre    []     = failwith msg
  in
    splrec [] 
  end;

(* *************************************************************************** *)

(* freezing and unfreezing *)

local 

   fun frz br = (ref_frz br):= Froz
   fun unf br = (ref_frz br):= UnFroz

in
   fun FreezeCxt ns cxt =
      let     
         fun freeze n = let val br = searchCxt n cxt
         	        in  frz br
		        end
      in  List.app freeze ns
      end

   fun UnfreezeCxt ns cxt =
      let
         fun unfreeze n = let val br = searchCxt n cxt
		      	  in  unf br
		     	  end
      in  if (null ns) then List.app unf cxt
       	  else List.app unfreeze ns
      end

end; 

(* ****************************************************************** *
val Dep_debug = ref false;
(* this has moved *) 

fun DEPENDS skip br_obj br_sbj cxt =
  let
    val nam = ref_nam br_obj
    fun Depends c =  (* DEEP dependency of a term on a name *)
    case c
      of (Ref br) =>
	(if (!Dep_debug)
	   then message("**Dep "^nam^" "^ref_nam br^" "^
			(Utils.concat_space (List.map ref_nam skip)))
	 else ();
	 DEPENDS skip br_obj br cxt)
       | (App((c,cs),_)) => (Depends c) orelse (List.exists Depends cs)
       | (Bind(_,_,c,d)) => (Depends d) orelse (Depends c)
       | (Tuple(T,l))    => (Depends T) orelse (List.exists Depends l) 
       | (CnLst l)       => List.exists Depends l
       | (Proj(_,c))     => Depends c
       | (RedTyp(_,c))   => Depends c
       | (Var(_,c))      => Depends c
       | _               => false
  in
    (not (List.exists (sameRef br_sbj) skip)) andalso
         ref_ts br_obj <= ref_ts br_sbj andalso
    (if (!Dep_debug)
       then message("**DEP "^nam^" "^ref_nam br_sbj^" "^
		    (Utils.concat_space (List.map ref_nam skip)))
     else ();
     sameRef br_sbj br_obj orelse
     let val (v,t) = ref_vt br_sbj
     in  Depends v orelse Depends t
     end orelse
       List.exists (fn br => DEPENDS (br_sbj::skip) br_obj br cxt)
           (List.map (fn nam => searchCxt nam cxt) (ref_deps br_sbj)))    (** ??? **)
  end;
 * ******************************************************************* *)

(* *************************************************************************** *
 * *************************************************************************** *)

(* *************************************************************************** *
 * *************************************************************************** *)
   end;

end;
