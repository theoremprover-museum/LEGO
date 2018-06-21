(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* conor-voodoo.sml *)

functor FunVoodoo( 
	structure Term:TERM
	structure Toc:TOC
	sharing 
		type Term.cnstr
		   = Toc.cnstr
	) 
(* *** * 
structure Voodoo 
 * *** *)
	: VOODOO 

 = 

struct 

       structure Term = Term 

  type voolabel = string * int

  datatype voodoo = VooBot
  | Voo of voolabel               (* herein lies the voodoo *)
  | VProp
  | VTheory                                  (* the type of theories *)
  | VType of Universes.node
  | VRef of Term.binding
  | VRel of int                                         (* variable *)
  | VApp of (voodoo * (voodoo list)) * (Term.prntVisSort list) (* application *)
  | VBind of Term.bindVisSort * string * voodoo * voodoo
  | VVar of int * voodoo                      (* existential variable *)
  | VTuple of voodoo * (voodoo list)           (* elem of Sig *)
  | VProj of Term.projSort * voodoo
  | VLabVT of Term.label * voodoo * voodoo          (* labeled trm:typ pair *)
  | VCnLst of voodoo list                     (* for use in Theories *)
  | VRedTyp of Term.instrs * voodoo   (* reduce the synthesised type using insts *)
  | VCase of voodoo * voodoo        (* case *)

  type voobind = voolabel * Term.bindVisSort * string * voodoo
  type vooctxt = voobind list
  type voostate = vooctxt * voodoo

  exception too_much_voodoo
  exception missing_voodoo
  exception voodoo_no_rewrite

local 

      val bug = Utils.Except.bug 
		
      val message = Printing.message
		
      val pri = Printing.pri
      val prs = Printing.prs
      val print = prs

		open Term 

      val toc = Toc.type_of_constr 

in 

        fun vooprint (Voo (s,j)) = ((print ("V-"^s));(pri j))
	| vooprint VProp = print "Prop"
	| vooprint VTheory = print "Theory"
	| vooprint (VType a) = print "Type(?)"
	| vooprint (VRef a) = print (ref_nam a)
	| vooprint (VRel j) = ((print "R");(pri j))
	| vooprint (VApp ((a,al),vl)) =
	  ((print "(");(vooprint a);
	   (List.map (fn x => ((print " ");(vooprint x))) al);(print ")"))
	| vooprint (VBind ((b,_),s,t,r)) =
	  ((case b of
		Pi => ((print ("{"^s^":"));(vooprint t);(print "}"))
	      | Lda => ((print ("["^s^":"));(vooprint t);(print "]"))
	      | Sig => ((print ("<"^s^":"));(vooprint t);(print ">"))
	      | _ => ((print ("!"^s^":"));(vooprint t);(print "!")));
		(vooprint r))
	| vooprint (VVar (a,b)) = ((print "(?");(pri a);(print ":");
	                           (vooprint b);(print ")"))
	| vooprint (VTuple (a,al)) =
	  ((print "(");(vooprint (hd al));
	   (List.map (fn x => ((print ",");(vooprint x))) (tl al));
	   (print ")"))
	| vooprint _ = print "!"

      fun vooprintstate ([],vt) =
	  ((print "tail : ");(vooprint vt);(print "\n"))
	| vooprintstate (((s:string,i:int),(b,_),nam,u)::t,vt) =
	  ((print s);(pri i);
	   (print (case b of Pi => " P" | Lda => " L" |
                             Sig => " S" | _ => " !"));
	   (print (" "^nam^" : "));(vooprint u);(print "\n");
	   (vooprintstate (t,vt)))

val sv_debug = ref false;      (* sameVoo *)

  fun sameVoo c d =
    let
(*      val an = !UVARS *)
      fun flre opn = if (!sv_debug) then opn() else ()
      val _ = flre (fn()=> (prs"**sV_deb t l: "; vooprint c;
			    prs"         t r: "; vooprint d))
      fun samVoo cd =
	case cd of (VooBot,VooBot) => bug"UM,samVoo;Bot"
	| (VBind((bt1,_),_,l1,r1),VBind((bt2,_),_,l2,r2)) =>
	    (if bt1=bt2 then true
	     else (flre (fn()=> message"**sV_deb f: bind type"); false))
	    andalso samVoo (l1,l2) andalso samVoo (r1,r2)
	| (VRef br1,VRef br2) =>
	    if sameRef br1 br2 then true
	    else (flre (fn()=> message("**sV_deb f: VRef "^
				       (ref_nam br1)^" "^(ref_nam br2)));
		  false)
	| (VRel n1,VRel n2) =>
	    if n1=n2 then true
	    else (flre (fn()=> message("**sV_deb f: Rel "^
				       (Int.toString n1)^" "^(Int.toString n2)));
		  false)
	| (VTuple(t1,cs1),VTuple(t2,cs2)) =>
	    (samVoo(t1,t2) andalso List.all samVoo (ListPair.zipEq (cs1,cs2))
	     handle ListPair.UnequalLengths =>
	       (flre (fn()=> message"**sV_deb f: Tuple"); false))
	| (VType n1,VType n2) =>
	    if (Universes.univ_cmp n1 n2) (* 2011: univ_cmp *)
	      then true
	    else (flre (fn()=> message"**sV_deb f: TypeType"); false)
	| (VProp,VType _) =>
	    if !Theories.LuosMode then true
	    else (flre (fn()=> message"**sV_deb f: PropType"); false)
	| (VProp,VProp) => true
	| (VTheory,VTheory) => true
	| (VApp((f1,as1),_),VApp((f2,as2),_)) =>
	    (samVoo(f1,f2) andalso List.all samVoo (ListPair.zipEq (as1,as2))
	     handle ListPair.UnequalLengths =>
	       (flre (fn()=> message"**sV_deb f: VApp"); false))
	| (VProj(p1,t1),VProj(p2,t2)) =>
	    (if p1=p2 then true
	     else (flre (fn()=> message"**sV_deb f: proj"); false))
	    andalso samVoo(t1,t2)
	| (VRedTyp(_,c1),VRedTyp(_,c2)) => samVoo(c1,c2)
	| (VVar(n,_),VVar(m,_)) =>
	    if n=m then true
	    else (flre (fn()=> message("**sV_deb f: Var "^
				       (Int.toString n)^" "^(Int.toString m)));
		  false)
	| (VLabVT(l1,c1,t1),VLabVT(l2,c2,t2)) =>
	    (if l1=l2 then true
	     else (flre (fn()=> message"**sV_deb f: LabVT"); false))
	    andalso samVoo(c1,c2) andalso samVoo(t1,t2)
	| (VCnLst cs1,VCnLst cs2) =>
	    (List.all samVoo (ListPair.zipEq (cs1,cs2))
	     handle ListPair.UnequalLengths =>
	       (flre (fn()=> message"**sV_deb f: CnLst"); false))
	| (Voo (s,i), Voo (t,j)) => s=t andalso i=j
	| (x,y) =>
	     (flre (fn()=> (prs"**sV_deb f l: "; vooprint x;
			    prs"         f r: "; vooprint y));
	      false)
    in 
(*       samVoo (c,d) orelse (UVARS:= an; false) *)
	 Universes.tryUniverses samVoo (c,d)
    end;

local
      fun mapsublist P f=
	  let
	      fun msl2 [] = []
		| msl2 (h::t) = if P h then (f h)::(msl2 t) else msl2 t
	  in
	      msl2
	  end
(* 
      local
	  exception not_mem
	  fun split i [] = raise not_mem
	    | split i (h::t) = if i=h then ([h],t)
			       else let
					val (l,m) = split i t
				    in
					(h::l,m)
				    end
      in
	  fun merge [] l = l
	    | merge (h::t) l =
	      let
		  val (p,s) = split h l
	      in
		  p@(merge t s)
	      end handle not_mem => h::(merge t l)
      end
 *)
  in
      fun voofold i v f =
	  let
	      fun vf (Voo j) = v j
		| vf (VApp ((a,al),_)) = vff (vf a) al
		| vf (VBind (_,_,a,b)) = f (vf a) (vf b)
		| vf (VVar (_,a)) = vf a
		| vf (VTuple (a,al)) = vff (vf a) al
		| vf (VProj (_,a)) = vf a
		| vf (VLabVT (_,a,b)) = f (vf a) (vf b)
		| vf (VCnLst al) = vff i al
		| vf (VRedTyp (_,a)) = vf a
		| vf (VCase (a,b)) = f (vf a) (vf b)
		| vf _ = i
	      and vff x [] = x
		| vff x (h::t) = vff (f x (vf h)) t
	  in
	      vf
	  end
      local
	  fun do_voo              Prop = VProp
	    | do_voo            Theory = VTheory
	    | do_voo          (Type a) = VType a
	    | do_voo           (Ref a) = VRef a
	    | do_voo           (Rel j) = VRel j
	    | do_voo (App ((a,al),vl)) = VApp ((do_voo a,List.map do_voo al),vl)
	    | do_voo  (Bind (b,s,t,r)) = VBind (b,s,do_voo t,do_voo r)
	    | do_voo       (Var (a,b)) = VVar (a,do_voo b)
	    | do_voo    (Tuple (a,al)) = VTuple (do_voo a,List.map do_voo al)
	    | do_voo      (Proj (a,b)) = VProj (a,do_voo b)
	    | do_voo   (LabVT (l,a,b)) = VLabVT (l,do_voo a,do_voo b)
	    | do_voo        (CnLst al) = VCnLst (List.map do_voo al)
	    | do_voo    (RedTyp (a,b)) = VRedTyp (a,do_voo b)
	    | do_voo      (Case (a,b)) = VCase (do_voo a,do_voo b)
	    | do_voo               Bot = VooBot
      in
	  fun start c = ([],do_voo c)
	  fun voo c = #2 (start c)

      end
      local
	  fun noovoo l =
	      let
		  fun noov i            (Voo j) = Voo j
		    | noov i              VProp = VProp
		    | noov i            VTheory = VTheory
		    | noov i          (VType a) = VType a
		    | noov i           (VRef a) = VRef a
		    | noov i           (VRel j) = if i=j then Voo l
						  else VRel j
		    | noov i (VApp ((a,al),vl)) =
		      VApp ((noov i a,List.map (noov i) al),vl)
		    | noov i  (VBind (b,s,t,r)) = VBind (b,s,noov i t,
							 noov (i+1) r)
		    | noov i       (VVar (a,b)) = VVar (a,noov i b)
		    | noov i    (VTuple (a,al)) =
		      VTuple (noov i a,List.map (noov i) al)
		    | noov i      (VProj (a,b)) = VProj (a,noov i b)
		    | noov i   (VLabVT (l,a,b)) = VLabVT (l,noov i a,noov i b)
		    | noov i        (VCnLst al) = VCnLst (List.map (noov i) al)
		    | noov i    (VRedTyp (a,b)) = VRedTyp (a,noov i b)
		    | noov i      (VCase (a,b)) = VCase (noov i a,noov i b)
		    | noov i             VooBot = VooBot
	      in
		  noov 1
	      end
	  fun intro1 (s,i) (vl,(VBind (b,nam,t,r))) =
	      let
		  val nam' = if nam="" then s^(Int.toString i) else nam
	      in
		  (vl@[((s,i),b,nam',t)],noovoo (s,i) r)
	      end
	    | intro1 _ _ = raise too_much_voodoo
      in
	  fun introvoo s 0 S = S
	    | introvoo s n S = intro1 (s,n) (introvoo s (n-1) S)
      end

      fun stop (vc,vt) =
	  let
	      fun get done (i:voolabel) =
		  let
		      fun g2 _ [] = raise missing_voodoo
			| g2 j (h::t) = if i=h then j
					else g2 (j+1) t
		  in
		      g2 1 done
		  end
	      fun un_voo g =
		  let
		      fun uv i (Voo j) = Rel (i+(g j))
			| uv i VProp = Prop
			| uv i VTheory = Theory
			| uv i (VType a) = Type a
			| uv i (VRef a) = Ref a
			| uv i (VRel j) = Rel j
			| uv i (VApp ((a,al),vl)) =
		          App ((uv i a,List.map (uv i) al),vl)
			| uv i (VBind (b,s,t,r)) =
			  Bind (b,s,uv i t,uv (i+1) r)
			| uv i (VVar (a,b)) = Var (a,uv i b)
			| uv i (VTuple (a,al)) =
			  Tuple (uv i a,List.map (uv i) al)
			| uv i (VProj (a,b)) = Proj (a,uv i b)
			| uv i (VLabVT (l,a,b)) =
			  LabVT (l,uv i a,uv i b)
			| uv i (VCnLst al) = CnLst (List.map (uv i) al)
			| uv i (VRedTyp (a,b)) = RedTyp (a,uv i b)
			| uv i (VCase (a,b)) =
			  Case (uv i a,uv i b)
			| uv i VooBot = Bot
		  in
		      uv
		  end
	      fun rebind done [] = rewind done vt 
		| rebind done ((i,b,s,t)::r) =
		  Bind (b,s,rewind done t,
			rebind (i::done) r)

	      and rewind done vt = un_voo (get done) 0 vt
	  in
	      rebind [] vc
	  end

      fun vootype v = voo ((toc) (stop ([],v))) (* 2011: !toc removed *)

      fun voorewrite f =
	  let
	      fun hit v = (f v) handle voodoo_no_rewrite => split v
	      and split (VApp ((v,vl),pl)) = VApp ((hit v,List.map hit vl),pl)
		| split (VBind (b,s,u,v)) = VBind (b,s,hit u,hit v)
		| split (VVar (i,v)) = VVar (i,hit v)
		| split (VTuple (v,vl)) = VTuple (hit v,List.map hit vl)
		| split (VProj (p,v)) = VProj (p,hit v)
		| split (VLabVT (l,u,v)) = VLabVT (l,hit u,hit v)
		| split (VCnLst vl) = VCnLst (List.map hit vl)
		| split (VRedTyp (i,v)) = VRedTyp (i,hit v)
		| split (VCase (u,v)) = VCase (hit u,hit v)
		| split v = v
	  in
	      hit
	  end
      fun voolift f (vc,vt) =
	  let
	      fun fc [] = []
		| fc ((i,b,s,h)::t) = (i,b,s,f h)::(fc t)
	  in
	      (fc vc,f vt)
	  end
      fun voomap v =
	  let
	      fun vm (Voo j) = v j
		| vm _ = raise voodoo_no_rewrite
	  in
	      voorewrite vm
	  end
      fun sub i v =
	  voolift (voomap (fn j => if i=j then v else (Voo j)))
      fun shove (x as (i,b,s,v)) rightofhere (vc,vt) =
	  let
	      fun righter j k =
		  if j=i then k
		  else if k=i then j
		       else
			   let
			       fun r2 [] = raise missing_voodoo
				 | r2 ((l,_,_,_)::t) =
				   if j=l then k
				   else if k=l then j
					else r2 t
			   in
			       r2 vc
			   end
	      val whereitis = voofold rightofhere (fn j => j) righter v
	      fun go [] = raise missing_voodoo
		| go ((h as (j,_,_,_))::t) =
		  if j=whereitis then h::x::t else h::(go t)
	  in
	      if whereitis=i then (x::vc,vt)
	      else (go vc,vt)
	  end
      fun fetch (i:voolabel) (vc,_) =
	  let
	      fun f2 [] = raise missing_voodoo
		| f2 ((h as (j,_,_,_))::t) =
		  if i=j then h else f2 t
	  in
	      f2 vc
	  end
      fun swap (x as (i:voolabel,_,_,_)) (vc,vt) =
	  let
	      fun s2 [] = raise missing_voodoo
		| s2 ((h as (j,_,_,_))::t) =
		  if i=j then x::t else h::(s2 t)
	  in
	      (s2 vc,vt)
	  end
      fun elide (i:voolabel) (vc,vt) =
	  let
	      fun e2 [] = raise missing_voodoo
		| e2 ((h as (j,_,_,_))::t) =
		  if i=j then t else h::(e2 t)
	  in
	      (e2 vc,vt)
	  end
      val dep1l = voofold [] (fn x => [x]) (fn l => fn m => l@m)
      fun dep1g C i =
	  mapsublist
	  ((voofold false (fn j => i=j) (fn a => fn b => a orelse b)) o
	   (fn (_,_,_,t) => t))
	  (fn (i,_,_,_) => i)
	  C
      local
      (* 
	  fun mem i [] = false
	    | mem i (h::t) = i=h orelse mem i t
	    *)
      in
	  fun deple [] = (fn k => [k])
	    | deple ((h as (n,_,_,_))::t) =
	      let
		  val prev = deple t
		  fun next l j = 
		      let
			  val pj = prev j
			  fun n2 [] = pj
			    | n2 (i::u) = if Utils.ListUtil.member i pj then n::pj
					  else n2 u
		      in
			  n2 l
		      end
	      in
		  next (dep1g t n)
	      end
      end
(*
      fun vooprint (Voo (s,j)) = ((print ("V-"^s));(print j))
	| vooprint (VProp) = print "Prop"
	| vooprint (VTheory) = print "Theory"
	| vooprint (VType a) = print "Type(?)"
	| vooprint (VRef a) = print (ref_nam a)
	| vooprint (VRel j) = ((print "R");(print j))
	| vooprint (VApp ((a,al),vl)) =
	  ((print "(");(vooprint a);
	   (List.map (fn x => ((print " ");(vooprint x))) al);(print ")"))
	| vooprint (VBind ((b,_),s,t,r)) =
	  ((case b of
		Pi => ((print ("{"^s^":"));(vooprint t);(print "}"))
	      | Lda => ((print ("["^s^":"));(vooprint t);(print "]"))
	      | Sig => ((print ("<"^s^":"));(vooprint t);(print ">"))
	      | _ => ((print ("!"^s^":"));(vooprint t);(print "!")));
		(vooprint r))
	| vooprint (VVar (a,b)) = ((print "(?");(print a);(print ":");
	                           (vooprint b);(print ")"))
	| vooprint (VTuple (a,al)) =
	  ((print "(");(vooprint (hd al));
	   (List.map (fn x => ((print ",");(vooprint x))) (tl al));
	   (print ")"))
	| vooprint _ = print "!"
      fun vooprintstate ([],vt) =
	  ((print "tail : ");(vooprint vt);(print "\n"))
	| vooprintstate (((s:string,i:int),(b,_),nam,u)::t,vt) =
	  ((print s);(print i);
	   (print (case b of Pi => " P" | Lda => " L" |
                             Sig => " S" | _ => " !"));
	   (print (" "^nam^" : "));(vooprint u);(print "\n");
	   (vooprintstate (t,vt)))
 *)
  end
end

end; (* struct *)