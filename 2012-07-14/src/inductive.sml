(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* ind_relations.sml *)

functor FunInductive (structure Term:TERM
		      structure Concrete:CONCRETE
		      structure Namespace:NAMESPACE
		      sharing 
		      	      type Term.cnstr
			      	 = Concrete.cnstr
			      	 = Namespace.cnstr
		      and 
			      type Term.Prefix
			      	 = Concrete.Prefix
		      and 
			      type Term.Frz
			      	 = Concrete.Frz
		      and 
			      type Term.LocGlob
			      	 = Concrete.LocGlob
		      and 
			      type Term.bindSort
			      	 = Concrete.bindSort
		      and 
			      type Term.visSort
			      	 = Concrete.visSort
		      and 
			      type Term.prntVisSort
			      	 = Concrete.prntVisSort
		      and 
			      type Term.projSort
			      	 = Concrete.projSort
		      ) 
(* *** * 
structure Inductive
 * *** *)
	: INDUCTIVE 

 = 
    struct
	local

	      val bug = Utils.Except.bug 

	      val succ = Utils.Counting.succ

	      val member = Utils.ListUtil.member
	      val mem_assoc = Utils.ListUtil.mem_assoc
	      val filter_pos = Utils.ListUtil.filter_pos 
	      val filter_neg = Utils.ListUtil.filter_neg 

	      val message = Printing.message
	      val prs = Printing.prs

		open Term 

	    (* open Concrete *)

	    val ref_c = Concrete.mkRef_c
	    val mkPiExp_c = Concrete.mkPiExp_c 
	    val mkLdaExp_c = Concrete.mkLdaExp_c 
	    val mkApp_c = Concrete.mkApp_c
	    val mkAppNoShow_c = Concrete.mkAppNoShow_c
	    val mkLift_c = Concrete.mkLift_c
	    val mkNewVar_c = Concrete.NewVar_c
	    val app_c = Concrete.App_c
	    val red_c = Concrete.mkRed_c
	    val cast_c = Concrete.Cast_c
	    val bind_c = Concrete.mkBind_c 
	    val prop_c = Concrete.Prop_c

	    (* open Namespace *) 

	    val mkNameGbl = Namespace.mkNameGbl

	in
	    type cnstr_c   = Concrete.cnstr_c

	    type Prefix = Term.Prefix
	    type Frz = Term.Frz
	    type LocGlob = Term.LocGlob
	    type visSort = Term.visSort
	    type prntVisSort = Term.prntVisSort
	    type projSort = Term.projSort

(* ******************************************** *)

	    type 'b binder = Prefix * string list * 'b 
	    type 'b ctxt   = 'b binder list

	    type binder_c = Concrete.binder_c
	    type ctxt_c = Concrete.ctxt_c

	    val unBind = Concrete.unBind : binder_c -> cnstr_c binder
	    val mkBind = Concrete.mkBind : cnstr_c binder -> binder_c

	    val mkCtxt = Concrete.mkCtxt o (List.map mkBind)
	    val unCtxt = (List.map unBind) o Concrete.unCtxt

(* ******************************************** *)

(* tidying up code -- no major changes *)

(* Modified version of datatype.sml to get something for inductive
   relations *)

(* Signature of this module is the function do_inductive_type which takes
   3 ctxt_c lists and a boolean and returns a ctxt_c list
   paired with a reduction   *)

(* schema_head is not just a string, but a string
   applied to some arguments.... *)
datatype schema_head =
  Head of string 
| Appl_a of prntVisSort * schema_head * cnstr_c;

(* This is a variant on the concrete syntax cnstr_c
   in parser.sml; with account taken of schema
   variables *)
  
datatype schema_c =
  Ref_s of schema_head  (* A schema variable *)
| Bind_s of cnstr_c binder * schema_c  (* Simple binding (x:K) where
				  K is not a schema *)
| Bind_sc of schema_c binder * schema_c  (* Complex binding by a schema *)

(*
withtype binder_c = cnstr_c binder 
    (* bindSort * visSort * frzLocGlob * string list * string list * cnstr_c *)

and binder_s = schema_c binder 
    (* bindSort * visSort * frzLocGlob * string list * string list * schema_c; *)
 *)
exception sch_err of string;

(* A function to test whether or not a term contains
   the schema variable, first argument is the list of
   schema variables *)

(* 2011 version *)
fun contains l v_c = Concrete.contains l v_c
    handle Concrete.getConcrete => raise sch_err "Metavariables not allowed here" 
    	 | Concrete.errConcrete => raise sch_err "error in contains"; 

(* 1998 version *
fun contains l (Concrete.Prop_c)         = false |
    contains l (Concrete.Type_c(_))      = false |
    contains l (Concrete.TypeAbs_c(_))   = false |
    contains l (Concrete.Ref_c(x))       = member x l|
    contains l (Concrete.App_c(_,c1,c2)) = (contains l c1) orelse (contains l c2) |
    contains l (Concrete.Bind_c((_,_,_,_,l1,c1),c2)) =
     (contains (filter_neg (fn x => member x l1) l) c1) 
                                  orelse (contains l c2)  |
    contains l (Concrete.Tuple_c (l1,c)) = (contains l c) orelse 
       foldr (fn x => (fn y => contains l x orelse y)) false l1 |
    contains l (Concrete.Proj_c(p,c))    = contains l c |
    contains l (Concrete.Cast_c(c1,c2))  = (contains l c1) orelse (contains l c2) |
    contains l (Concrete.Var_c(_))   = raise sch_err "Metavariables not allowed here" |
    contains l Concrete.NewVar_c     = raise sch_err "Metavariables not allowed here" |
    contains l Concrete.Bot_c        = false |
    contains l _                     = raise sch_err "error in contains";
 *)


(* This function should convert a term in cnstr_c into
   a schema term given the list of schematic variables l *)

(* NB invariant: these are only called if isHead holds *)

(* 2011 version *)
fun map_ref_to_schema_head l v_c = 
    let 
       val x = Concrete.getRefNam v_c
    in 
       if member x l then Head(x) else
          raise sch_err "Not a valid schema"
    end; (* handle Concrete.getConcrete => raise sch_err "Not a valid schema"; *)

fun map_cnstr_to_schema_head l v_c = (* it's an App_c or a Ref_c *)
    let 
       val (x,c,c1) = Concrete.getAppData v_c
    in 
       if (contains l c1) then raise sch_err "Not a valid schema"
	   else Appl_a(x,(map_cnstr_to_schema_head l c),c1) 
    end handle Concrete.getConcrete => map_ref_to_schema_head l v_c;  


(* 1998 version *
fun map_cnstr_to_schema_head l (Concrete.Ref_c(x)) = if member x l then Head(x) else
          raise sch_err "Not a valid schema" 
  | map_cnstr_to_schema_head l (Concrete.App_c(x,c,c1)) =
           if (contains l c1) then raise sch_err "Not a valid schema"
	   else Appl_a(x,(map_cnstr_to_schema_head l c),c1) 
  | map_cnstr_to_schema_head l _ =  raise sch_err "Not a valid schema";
 *)	
	   
(* 2011 version *)
fun map_cnstr_to_schema l v_c = 
    if Concrete.isHead v_c
       then Ref_s(map_cnstr_to_schema_head l v_c)
    else let
    	    val (((prefix as Prefix(Pi,_,_,_,_)),l2,c1),c2) = Concrete.getBinder v_c
    	 in 
            if (contains l c1) then 
                Bind_sc((prefix,l2,(map_cnstr_to_schema l c1)),
		        (map_cnstr_to_schema l c2))
            else
            Bind_s((prefix,l2,c1),(map_cnstr_to_schema l c2))
	 end
    handle _ => raise sch_err "Not a valid schema"; (* can raise Match/getConcrete *)


(* 1998 version *
fun map_cnstr_to_schema l (Concrete.Bind_c((Pi,b,c,l1,l2,c1),c2)) =
        if (contains l c1) then 
                Bind_sc((Pi,b,c,l1,l2,(map_cnstr_to_schema l c1)),
		        (map_cnstr_to_schema l c2))
        else
            Bind_s((Pi,b,c,l1,l2,c1),(map_cnstr_to_schema l c2))
  | map_cnstr_to_schema l (Concrete.Ref_c(s))     =
      if member s l then Ref_s(Head(s))
      else raise sch_err "Not a valid schema"
  | map_cnstr_to_schema l (Concrete.App_c(x,a,b)) =
      Ref_s(map_cnstr_to_appl l (Concrete.App_c(x,a,b)))
  | map_cnstr_to_schema l _ = raise sch_err "Not a valid schema";
 *)	 

(* Substitution of b for a in concrete term c is
   subst (a,b) c *)

(* 2011 version *)
fun subst_c l v_c = Concrete.subForNam l v_c
    handle Concrete.getConcrete => raise sch_err "Metavariables not allowed here"
         | Concrete.errConcrete => raise sch_err "error in subst_c";
  
(* 1998 version *
fun subst_c l (Concrete.Prop_c)         = Concrete.Prop_c |
    subst_c l (Concrete.Type_c(s))      = Concrete.Type_c(s) |
    subst_c l (Concrete.TypeAbs_c(x))   = Concrete.TypeAbs_c(x) |
    subst_c (a,b) (Concrete.Ref_c(x))   = if a=x then Concrete.Ref_c(b) else Concrete.Ref_c(x) |
    subst_c l (Concrete.App_c(x,c1,c2)) = 
              Concrete.App_c(x,(subst_c l c1),(subst_c l c2)) |
    subst_c (a,b) (Concrete.Bind_c((x,y,c,d,l1,c1),c2)) =
                  if (member a l1) then bind_c((x,y,c,d,l1,c1),c2)
      else bind_c((x,y,c,d,l1,(subst_c (a,b) c1)),(subst_c (a,b) c2)) |
    subst_c l (Concrete.Tuple_c(l1,c)) = Concrete.Tuple_c(List.map (fn x => (subst_c l x)) l1,
					(subst_c l c))  |
    subst_c l (Concrete.Proj_c(p,c))   = Concrete.Proj_c(p,subst_c l c) |
    subst_c l (Concrete.Cast_c(c1,c2)) = Concrete.Cast_c((subst_c l c1),(subst_c l c2)) |
    subst_c l (Concrete.Var_c(_)) = raise sch_err "Metavariables not allowed here" |
    subst_c l Concrete.NewVar_c   = raise sch_err "Metavariables not allowed here" |
    subst_c l Concrete.Bot_c      = Concrete.Bot_c |
    subst_c l _          = raise sch_err "error in subst_c";
 *)

(* Similarly, but for schemas too *)

fun subst_app l (sch as Head(x)) = sch 
  | subst_app l (Appl_a(x,a,c))  = Appl_a(x,(subst_app l a),subst_c l c);
    
fun subst_s l (Ref_s(x)) = Ref_s(subst_app l x) 
  | subst_s (a,b) (Bind_s((pfx,l1,c1),s2)) =
         if (member a l1) then  Bind_s((pfx,l1,c1),(subst_s (a,b) s2))
         else Bind_s((pfx,l1,(subst_c (a,b) c1)),(subst_s (a,b) s2)) 
  | subst_s (a,b) (Bind_sc((pfx,l1,s1),s2)) =
         if (member a l1) then  Bind_sc((pfx,l1,s1),(subst_s (a,b) s2))
         else Bind_sc((pfx,l1,(subst_s (a,b) s1)),(subst_s (a,b) s2));

fun subst_c_list [] cnstr = cnstr 
  | subst_c_list (s::l) cnstr = subst_c_list l (subst_c s cnstr);
    
fun subst_s_list [] cnstr = cnstr 
  | subst_s_list (s::l) cnstr = subst_s_list l (subst_s s cnstr);

(* 2011 version *)
fun binders_ind v_c = 
   let
      val ((Prefix(_,d,_,_,_),l,s1),s) = Concrete.getBinder v_c
   in 
      (List.map (fn x => (x,s1,d)) l)@(binders_ind s)
   end handle getConcrete => [];
  
(* 1998 version *
fun binders_ind (Concrete.Bind_c(bd,s)) = 
    let val (_,d,_,_,l,s1) = (* unBind *) bd
    in  (List.map (fn x => (x,s1,d)) l)@(binders_ind s)
    end
  | binders_ind (_) = [];
 *)
  
(* outputs a (string,constr_c) list  *)

fun start_T_of_C l  str = (* 2011: List.foldl *)
    List.foldl (fn ((a,_,d),x) => app_c((prVis d),x,ref_c(a))) (ref_c(str)) l;
       
fun T_of_C l str typestr = 
    List.foldr  
      (fn ((a,b,_),x) => mkPiExp_c Hid Local [a] b x)
      (mkPiExp_c Vis Local [""] (start_T_of_C l str) (typestr)) l;

(*
  List.foldr  (fn ((a,b,_),x) => bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x))
   (bind_c((Pi,Vis,(UnFroz,Local),[],[""],(start_T_of_C l str)),(typestr))) l;
 *)
          
 
(* The type of ``C'' for an inductive type str with binders l *)

fun start_A_of_C l str = (* 2011: List.foldl *)
    List.foldl
      (fn ((a,_,_),x) => mkAppNoShow_c(x,ref_c(a)))
      (ref_c("C_"^str)) l;
(*
   foldl  (fn x => (fn (a,_,_) => app_c (NoShow,x,ref_c(a))))
   (ref_c("C_"^str)) l;
 *)

fun Univer_of_C l str = (* 2011: List.foldr *)
   List.foldr  
      (fn ((a,b,_),x) => mkPiExp_c Hid Local [a] b x)
      (mkPiExp_c Vis Local ["z"] (start_T_of_C l str) 
         (mkApp_c((start_A_of_C l str), ref_c("z")))) l; 
(*
  foldr (fn (a,b,_) => (fn x => bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x)))
  (bind_c((Pi,Vis,(UnFroz,Local),[],["z"],(start_T_of_C l str)),
            app_c(ShowNorm,(start_A_of_C l str),ref_c("z")))) l;
 *)

(* For debugging *)  

fun pr_cc c = ();   (***************************************)
val rec pr_app =
  fn Head(str) => prs str
  |  Appl_a(_,a,c) =>( pr_app a; prs" "; pr_cc c);
  
  
val rec pr_sc =
 fn Ref_s(str) => pr_app str 
  | Bind_s((pfx,y,c),d) => 
         (prs"(B," ;prs(hd y);prs":";pr_cc c;prs"'";pr_sc d;prs")")
  | Bind_sc((pfx,x,c),d) => 
         (prs"(B," ;prs(hd x);prs":";pr_sc c;prs"'";pr_sc d;prs")");


fun appl_to_type (Head(s)) = ref_c(s) |
    appl_to_type (Appl_a(x,a,c)) = app_c(x,(appl_to_type a),c);
    
fun schema_to_type (Ref_s(s)) = appl_to_type(s) |
    schema_to_type (Bind_s(b,s)) = bind_c(b,(schema_to_type s)) |
    schema_to_type (Bind_sc((pfx,m,s1),s2)) =
    bind_c((pfx,m,(schema_to_type s1)),(schema_to_type s2));
  
fun get_names [] = [] |
    get_names (((_,l,_):cnstr_c binder)::rest) = 
    l @ (get_names rest);

(* Supposed to massage bindings into appropriate form.
   Do everything with Global for now... *)

(* We can re-use get schema names to get names of
   types to make dependencies *)

(* 2011 version *)
fun get_end_type term = Concrete.getEndType term
    handle Concrete.getConcrete => raise sch_err "Unexpected type";

(* 1998 version *
fun get_end_type (Concrete.Bind_c(_,s)) = get_end_type s
 |  get_end_type (Concrete.Ref_c(s)) = Concrete.Ref_c(s)
 |  get_end_type (Concrete.Type_c(s)) = Concrete.Type_c(s)
 |  get_end_type (Concrete.Prop_c) = Concrete.Prop_c
 |  get_end_type (Concrete.TypeAbs_c(n)) = Concrete.TypeAbs_c(n)
 |  get_end_type _ = raise sch_err "Unexpected type";
 *)
      
(* 2011 version *)
fun subst_for_type st term = Concrete.subForType st term
    handle Concrete.getConcrete => raise sch_err "Unexpected type";


(* 1998 version *
fun subst_for_type st (Concrete.Bind_c(x,s)) = bind_c(x,(subst_for_type st s))
 |  subst_for_type st (Concrete.Type_c("")) = Concrete.Type_c(st)
 |  subst_for_type st _ = raise sch_err "Unexpected type";
 *)


(* 2011 version *)
fun get_end term = Concrete.getEnd term 
    handle Concrete.getConcrete => raise sch_err "Unexpected type";

(* 1998 version *
fun get_end (Concrete.Bind_c(_,s)) = get_end s
 |  get_end (Concrete.App_c(_,s,_)) = get_end s
 |  get_end (Concrete.Ref_c(s)) = s
 |  get_end _ = raise sch_err "Unexpected type";
 *)

fun look_up_type cn dn_binds = (* 2011: List.foldr *)
   let val find_it = get_end cn
   in 
     List.foldr
        (fn ((_,str,cn2),x) =>
               if member find_it str then 
                   get_end_type cn2 
               else x)
     (Concrete.mkType_c()) (* Concrete.Type_c("") modified to be theory-sensitive *)
     dn_binds end;
     
(* (Let,Def,(UnFroz,Local),[],["T"],Type_c) *)


(* 2011 version *)
fun do_cast cast_to v_c = 
   let 
      val ((pfx,l,cn),rest) = Concrete.getBinder v_c
   in 
      bind_c((pfx,l,cast_c(cn,cast_to)),(do_cast cast_to rest))
   end handle Concrete.getConcrete => v_c;
  
(* 1998 version *
fun do_cast cast_to (Concrete.Bind_c((a,b,c,d,l,cn),rest)) =
      bind_c((a,b,c,d,l,(cast_c(cn,cast_to))),(do_cast cast_to rest)) |
      do_cast cast_to x = x;
 *)

fun redo_bindings_with_dependency (safe:bool) (with_bindings:cnstr_c ctxt)
    (declaration_bindings:cnstr_c ctxt) (schema_bindings:cnstr_c ctxt) =
     let val dependent_names = get_names schema_bindings;

     val (new_declaration_bindings) = (* 2011: List.foldr *)
        List.foldr 
	(fn ((pfx,l,cn):cnstr_c binder,so_far:(cnstr_c ctxt)) =>
         (if (Concrete.isTYPE (get_end_type cn)) (* *** !!! *** *)
           then ((List.map (fn name => 
                       (pfxUnfGlb dependent_names pfx,[name],
	                subst_for_type name cn)) l)
	         @so_far)
          else ((pfxUnfGlb dependent_names pfx,l,cn)::so_far)
	  ))
       ([])
       declaration_bindings;
    (* a should always be Let and cn Type (or maybe Prop...) here *)

     val new_schema_bindings =
          List.map (fn (pfx,l,cn) => 
                   (pfxUnfGlb0 pfx,l,
          (if safe then
             (do_cast (look_up_type cn new_declaration_bindings) cn )
             else cn) ))
          schema_bindings 
     in
       (with_bindings@new_declaration_bindings@new_schema_bindings) (*: cnstr_c ctxt *)
     end;

 
(* No need for contexts here *)

(* So what we need is a function to convert the 3 concrete
   terms given as input to the datatype into schema_c,
   calculate from the schema_c terms the cnstr_c terms
   which make up the elimination and reduction rules,
   massage the bindings to get right dependency on the
   original 3 concrete bits and pass back 
    (1) The list of bindings (The type, its constructors and
   the elimination rule)
    (2) The reduction (another constr_c)
*)

(* 2011 version *)
fun make_type_nice n v_c = 
   let 
      val ((pfx,l,s1),s) = Concrete.getBinder v_c; 
      fun name n = ("x"^Int.toString n);
      fun chck_list n [] = (n,[]) 
        | chck_list n (a::l) = let 
	  	      	       	   val (m1,l1) = chck_list n l 
				in
				   if (a = "") 
                                      then (succ m1,((name m1)::l1))
		                   else (m1,(a::l1)) 
			       end; 
      val (new_n,new_l) = chck_list n l
   in 
      bind_c((pfx,new_l,s1),(make_type_nice new_n s))
   end handle Concrete.getConcrete => v_c;
  
(* 1998 version *
fun make_type_nice n (Concrete.Bind_c((a,b,c,d,l,s1),s)) = 
      let fun name n = ("x"^Int.toString n);
          fun chck_list n [] = (n,[]) |
                  chck_list n (a::l) = 
                       let val (m1,l1) = chck_list n l in
                             if (a = "") 
                                then (succ m1,((name m1)::l1))
		                else (m1,(a::l1)) end; 
         val (new_n,new_l) = chck_list n l  in           
	     (bind_c((a,b,c,d,new_l,s1),(make_type_nice new_n s))) end 
  | make_type_nice n x = x;
 *)  
	     

fun free_in_binder_list l ([](*:ctxt_c*)) = false |
    free_in_binder_list l ((_,l1,c1)::rest)  =
    ((contains (filter_neg (fn x => member x l1) l) c1))
    orelse (free_in_binder_list l rest);
  
fun make_name_list [] s_binds = [] |
    make_name_list (((_,l,c):cnstr_c binder)::rest) s_binds =
    (List.map (fn x => let fun mnrec m =
	  let val nn = x^Int.toString m
       in if (free_in_binder_list ["C_"^nn] s_binds) then mnrec (succ m) 
	  else nn end;
              val nice_c = make_type_nice 1 c
		  in
          if (free_in_binder_list ["C_"^x] s_binds) then
         ((mnrec 1),nice_c) else (x,nice_c) end)
        l)@(make_name_list rest s_binds);

fun make_disj_var_schema schema n =
   let fun name str n = let
             fun mnrec m =
                 let val nn = str^Int.toString m
                 in if (member nn n) then mnrec (succ m) 
                            else nn end in
				mnrec 1 end;
       fun chck_list n [] = ([],n,[]) |
           chck_list n (a::l) = 
                let val (subs,m1,l1) = chck_list n l in
                if member a m1 then     
                  let val newname = name a m1 in
                   ((a,newname)::subs,newname::m1,newname::l1) end 
               else (subs,a::m1,a::l1)  end;
       fun chck_names n ((pfx,m,cn)) = 
	   let val (subs,n1,m1) = 
                   chck_list n m in (subs,n1,(pfx,m1,cn)) end;
       fun sort_schema n (Ref_s(mm)) = (n,Ref_s(mm)) |
           sort_schema n (Bind_s(b,cn)) =
           let val (ss,m,nb) = chck_names n b;
	       val (m1,nsc) = sort_schema m cn
               in (m1,Bind_s(nb,(subst_s_list ss nsc))) end |
           sort_schema n (Bind_sc(b,sch)) =
	   let val (ss,m,(pfx,g,cn)) = chck_names n b ;
               val (m1,nsc) = sort_schema m cn;
	       val (m2,sc) = sort_schema m1 sch
          in (m2,Bind_sc((pfx,g,(subst_s_list ss nsc)),sc)) end 
   in  sort_schema n schema end;

(*  
val sche = Bind_s((Pi,Vis,(UnFroz,Local),[],["a"],Ref_c("A")),
    Bind_s((Pi,Vis,(UnFroz,Local),[],["x"],Ref_c("a")),Ref_s("list")));
    *)

fun make_disj_var_schemas schema_list =
   let fun do_stuff [] = ([],[]) |
           do_stuff ((str,S)::rest) =
           let val (n,nrest) = do_stuff rest;
               val (m,nschema) =  make_disj_var_schema S n   
                    in
	       (m,((str,nschema)::nrest)) end;
       val (x,nschema_list) = do_stuff schema_list
   in nschema_list end;

fun make_schema_list (declaration_bindings(*:ctxt_c*)) 
       (schema_bindings (*:ctxt_c*)) = (* 2011: List.foldr *)
    let val names = get_names declaration_bindings in
    List.foldr (fn ((_,l,cn):cnstr_c binder,rest) =>
       (let val S = (map_cnstr_to_schema names cn) in
       (List.map (fn x => (x,S)) l) end)@rest) nil
    schema_bindings
    end;

fun make_schema_nice schema n =
   let fun name n = ("x"^Int.toString n);
       fun chck_list n [] = (n,[]) 
         | chck_list n (a::l) = 
                 let val (m1,l1) = chck_list n l in
                      if (a = "") 
                      then (succ m1,((name m1)::l1))
		      else (m1,(a::l1)) end;
       fun chck_names n ((pfx,m,cn)) = 
	   let val (n1,m1) = chck_list n m in (n1,(pfx,m1,cn)) end;
       fun sort_schema n (Ref_s(mm)) = (n,Ref_s(mm)) 
         | sort_schema n (Bind_s(b,cn)) =
           let val (m,nb) = chck_names n b;
	       val (m1,nsc) = sort_schema m cn
               in (m1,Bind_s(nb,nsc)) end 
         | sort_schema n (Bind_sc(b,sch)) =
	   let val (m,(pfx,g,cn)) = chck_names n b ;
               val (m1,nsc) = sort_schema m cn;
	       val (m2,sc) = sort_schema m1 sch
                   in (m2,Bind_sc((pfx,g,nsc),sc)) end 
   in  sort_schema n schema end;

(*  
val sche = Bind_s((Pi,Vis,(UnFroz,Local),[],["",""],Ref_c("A")),
    Bind_sc((Pi,Vis,(UnFroz,Local),[],["",""],Ref_s("list")),Ref_s("list")));
    *)

fun nice_schemas schema_list =
   let fun do_stuff [] = (1,[]) |
           do_stuff ((str,S)::rest) =
           let val (n,nrest) = do_stuff rest;
               val (m,nschema) = make_schema_nice S n   
                    in
	       (m,((str,nschema)::nrest)) end;
       val (x,nschema_list) = do_stuff schema_list
   in nschema_list end;

      
(* Also want this to make a name up if l2 is "" or list of them 
  since this is needed in phizero *)

fun strictly_positive (Ref_s(_)) = true |
    strictly_positive (Bind_s(_,s)) = strictly_positive s |
    strictly_positive (Bind_sc(_,_)) = false;
  
fun valid_schema (Ref_s(_)) = true |
    valid_schema (Bind_s(_,s)) = valid_schema s  |
    valid_schema (Bind_sc((_,_,s1),s)) = valid_schema s  
    andalso strictly_positive s1;

fun arities (Ref_s(_)) = [] |
    arities (Bind_s(_,s)) = arities s |
    arities (Bind_sc((Prefix(_,y,_,_,_),l,s1),s)) = 
                      (List.map (fn x => (x,y,s1)) l)@(arities s);

fun binders (Ref_s(_)) = [] 
  | binders (Bind_s((Prefix(_,y,_,_,_),l,s1),s)) = 
      (List.map (fn x => (x,y,s1)) l)@(binders s) 
  | binders (Bind_sc((Prefix(_,y,_,_,_),l,s1),s)) = 
    (List.map (fn x => (x,y,(schema_to_type s1))) l)@(binders s);

fun gen_app z y (s::nil) = app_c((prVis y),z,ref_c(s)) 
  | gen_app z y (s::l) = gen_app (app_c((prVis y),z,ref_c(s))) y l 
  | gen_app z _ _ = raise sch_err "Something very wrong here";
    
fun get_name_app (Head(s)) = s |
    get_name_app (Appl_a(x,a,c)) = get_name_app a;

fun phizero (Ref_s(s)) z = mkApp_c(ref_c("C_"^(get_name_app s)),z)
  | phizero (Bind_s((Prefix(Pi,x,_,_,_),l,c),c1)) z =
             mkPiExp_c x Local l c (phizero c1 (gen_app z x l))
  | phizero _ z = raise sch_err "Schema is not strictly positive";
		     
fun phihash (Ref_s(s)) f z = mkApp_c(f,z) 
  | phihash (Bind_s((Prefix(Pi,x,_,_,_),l,c),c1)) f z =
             mkLdaExp_c x Local l c (phihash c1 f (gen_app z x l)) 
  | phihash _ f z = raise sch_err "Schema is not strictly positive";

fun get_name_and_type (Ref_s(s)) = (get_name_app s,s) 
  | get_name_and_type (Bind_s(_,s)) = get_name_and_type(s) 
  | get_name_and_type (Bind_sc(_,s)) = get_name_and_type(s) ;  
  
fun iota_of_a (x,S) = (* 2011: List.foldl *)
   List.foldl
   (fn ((name,x,cnstr2),cnstr) =>
        (app_c((prVis x),cnstr,ref_c(name))))
   (ref_c(x)) (binders S);
(*   
fun start_up c str ty l = 
    let
	fun stuff [] z = z |
	    stuff ((na,x,_)::m) z = 
	    stuff m (app_c((prVis x),z,ref_c(na)));  
    in 
	mkApp_c((apply_all (args_of_head ty) 
                    (ref_c("C_"^str))),(stuff l c)) end;
*)	
(* Bug in start_up....sorted out now  *)	
fun start_up S z str ty = 
     mkApp_c((ref_c("C_"^str)),(iota_of_a (z,S)));
     
fun thetazero S z =
  let 
    val l1 = binders S;
    val (name,ty) = get_name_and_type S;
    val l2 = arities S
  in (* 2011: List.foldr *)
    let val begin = List.foldr 
      (fn ((str,x,schema),z) =>
          mkPiExp_c x Local [str^"_ih"] (phizero schema (ref_c(str))) 
(* 
       (fn so_far => bind_c((Pi,x,(UnFroz,Local),[],[str^"_ih"],
			     (phizero schema (ref_c(str)))),
			    so_far))
 *)
			    z)
      (start_up S z name ty)
      l2
    in (* 2011: List.foldr *)
      List.foldr (fn ((name,x,cnstr),z) => 
         mkPiExp_c x Local [name] cnstr z 
(* 
	     fn so_far =>
	        bind_c((Pi,x,(UnFroz,Local),[],[name],cnstr),so_far)
 *)
             )
      begin
      l1
    end 
  end;
		    
fun eliminator schema_names name type_of_name list_of_schemas typestr =
    let val name_l = binders_ind type_of_name;
	val start_value = Univer_of_C name_l name;
	val innerpart = (* 2011: List.foldr *)
	   List.foldr 
	   (fn ((str,schema),z) => 
	    mkPiExp_c Vis Local [""] (thetazero schema str) z)
	   start_value 
	   list_of_schemas
    in
      List.foldr 
      (fn ((str,cnstr),z) =>
       mkPiExp_c Vis Local ["C_"^str] (T_of_C (binders_ind cnstr) str typestr) z)
      innerpart
      schema_names
    end;

fun eliminators schema_names list_of_schemas typestr =
  List.map (fn (str,cnstr) => 
       (Prefix(Lda,Vis,UnFroz,Global,[]),[str^"_elim"],
	(eliminator schema_names str cnstr list_of_schemas typestr)):cnstr_c binder)
  schema_names;
  
(* Need to elaborate ``schema_names'' so as to retain the
   type information from which derives type of ``C'' *)

(* Need something to force an argument into every Pi binding
   in a schema else create one... *)

fun first_bindings name_list typestr = 
   List.map (fn (str,cnstr) => 
    (Prefix(Lda,Vis,UnFroz,Local,[]),["C_"^str],
     (T_of_C (binders_ind cnstr) str typestr)):cnstr_c binder) name_list;

fun second_bindings schema_list =
    List.map (fn (str,schema) =>  
    (Prefix(Lda,Vis,UnFroz,Local,[]),[mkNameGbl("f_"^str)], 
     (thetazero schema str)):cnstr_c binder)
    schema_list;

fun third_bindings schema_list = (* 2011: List.foldr *)
   List.foldr (fn ((a,S),x) => 
        (List.map (fn (name,y,cnstr) => 
     (Prefix(Lda,y,UnFroz,Local,[]),[name],cnstr):cnstr_c binder) (binders S))@x) nil 
   schema_list;
   
fun all_bindings name_list schema_list typestr =
   List.concat [first_bindings name_list typestr,second_bindings schema_list,
		   third_bindings schema_list]

(* takes a constructor name and its schema and gives back
   what Luo calls ``\iota(bar{a})'', a cnstr_c '' *)

(* Should have eliminated the rev by using foldl...check this ! *)


fun recursor_applied_to_bindings name_list schema_list (x,S) = (* 2011: List.foldl *)
  let val (str,ty) = get_name_and_type S
  in
     (List.foldl (fn ((name,schema),cnstr) 
			  => (mkApp_c(cnstr,ref_c(mkNameGbl("f_"^name)))))
      (List.foldl (fn ((name,cnstr2),cnstr) =>
			   (mkApp_c(cnstr,ref_c("C_"^name))))
       (ref_c((str)^"_elim")) name_list)
      schema_list)
  end;

fun lhs_of_reduction name_list schema_list (x,S) =
  mkApp_c(
	(recursor_applied_to_bindings name_list schema_list (x,S)),
	(iota_of_a(x,S)));
  
fun rhs_of_reduction name_list schema_list (x,S) = (* 2011: List.foldl *)
  List.foldl 
  (fn ((name,y,schema),cnstr) =>
    app_c((prVis y),cnstr,(phihash schema   
			   (recursor_applied_to_bindings
			    name_list schema_list (name,schema))
			   (ref_c(name))))) 
  (List.foldl
   (fn ((name,y,cnstr2),cnstr) =>
     (app_c((prVis y),cnstr,(ref_c(name)))))
   (ref_c(mkNameGbl("f_"^x))) (binders S))
  (arities S);

fun make_reductions name_list schema_list typestr =
     red_c(mkCtxt (all_bindings name_list schema_list typestr),
   (List.map (fn (x,S) => 
     ((lhs_of_reduction name_list schema_list (x,S)),
      (rhs_of_reduction name_list schema_list (x,S))))
    schema_list));
    

fun do_old_inductive_type (safe:bool) (with_bindings(*:ctxt_c*))
                      (declaration_bindings(*:ctxt_c*))
                      (schema_bindings(*:ctxt_c*))
                      (is_relation:bool) 
                      (typestr:cnstr_c) = 
  let
    val with_bindings = unCtxt with_bindings
    val declaration_bindings = unCtxt declaration_bindings
    val schema_bindings = unCtxt schema_bindings
    val init_context = redo_bindings_with_dependency safe with_bindings
                                                     declaration_bindings
				                     schema_bindings
    val schema_list =
      nice_schemas (make_schema_list declaration_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list declaration_bindings schema_bindings
  in
    (mkCtxt(init_context @ (eliminators name_list schema_list typestr)),
     (if is_relation then (prop_c) 
      else (make_reductions name_list disj_sch_list typestr)))
 end;

(* ******************** *
fun do_inductive_type (with_bindings(*:ctxt_c*))
                      (declaration_bindings(*:ctxt_c*))
                      (schema_bindings(*:ctxt_c*))
                      (is_relation:bool) (typestr:cnstr_c) = 
      do_old_inductive_type false with_bindings declaration_bindings
      schema_bindings is_relation typestr;
      
fun do_safe_inductive_type (with_bindings(*:ctxt_c*))
                      (declaration_bindings(*:ctxt_c*))
                      (schema_bindings(*:ctxt_c*))
                      (is_relation:bool) (typestr:cnstr_c) = 
      do_old_inductive_type true with_bindings declaration_bindings
      schema_bindings is_relation typestr;
 * ******************** *)

(* relation.sml *)

(* tidying up code -- no major changes *)

(* Modified version of datatype.sml to get something for inductive
   relations *)

(* Signature of this module is the function do_inductive_type which takes
   3 ctxt_c lists and a boolean and returns a ctxt_c list
   paired with a reduction   *)

(* schema_head is not just a string, but a string
   applied to some arguments.... *)


fun nT_of_C l str typestr = (* 2011: List.foldr *)
  List.foldr  (fn ((a,b,v),x) => mkPiExp_c v Local [a] b x)
   (prop_c) l;

 (* Changed (typestr) to (prop_c) in above function, so that 
    elimination is only over Prop, no matter what you set TYPE and
    typestr to be.....*)          
(* The type of ``C'' for an inductive type str with binders l *)

fun nstart_A_of_C l str = (* 2011: List.foldl *)
   List.foldl (fn ((a,_,b),x) => app_c((prVis b),x,ref_c(a)))
   (ref_c("C_"^str)) l;

(* Conor hacked nUniver_of_C to hide the relation parameters in the
   conclusion of the elim rule, ie
      {x1|p1}...{xn|pn}(R x1 ... xn)->(C_R x1 ... xn)
   instead of
      {x1:p1}...{xn:pn}(R x1 ... xn)->(C_R x1 ... xn)                *)

fun nUniver_of_C l str = (* 2011: List.foldl *) 
    		 (* This Hid used to be v (sez Conor) *)
  List.foldr (fn ((a,b,v),z) => mkPiExp_c Hid Local [a] b z) 
  	(mkPiExp_c Vis Local ["z"] (start_T_of_C l str) (nstart_A_of_C l str)) 
	l;

fun app_of_schema_applied (Head(s)) z = z |
    app_of_schema_applied (Appl_a(x,a,c)) z =
    app_c(x,(app_of_schema_applied a z),c);

fun nphizero (Ref_s(s)) z = app_of_schema_applied s 
                     (ref_c("C_"^(get_name_app s)))
  | nphizero (Bind_s((Prefix(Pi,x,_,_,_),l,c),c1)) z =
        mkPiExp_c x Local l c (nphizero c1 z)
  | nphizero _ z = raise sch_err "Schema is not strictly positive";
(* Need to change this!!!! *)		     

(* Conor hacked nphihash to compensate for the hidden parameters in the
   conclusion of the elim rule                                       *)

fun nphihash (Ref_s(s)) f z = mkApp_c((*(app_of_schema_applied s f)*)
                                             (* Conor hacks again *)f,z)
  | nphihash (Bind_s((Prefix(Pi,x,_,_,_),l,c),c1)) f z = 
       mkLdaExp_c x Local l c (nphihash c1 f (gen_app z x l)) 
  | nphihash _ f z = raise sch_err "Schema is not strictly positive";

fun get_head (Ref_s(s)) = s 
  | get_head (Bind_s(_,s)) = get_head(s) 
  | get_head (Bind_sc(_,s)) = get_head(s) ;  

fun nstart_up S z str ty = let val s = get_head S in
    app_of_schema_applied s ((ref_c("C_"^(get_name_app s)))) end;

(* `nonarities' is Claire's function to filter out the inductive
   hypotheses we want to keep; we want to use `binders' instead,
   so that we get all the arguments to the constructor            *)

fun nonarities (Ref_s(_)) = [] 
  | nonarities (Bind_s((Prefix(_,y,_,_,_),l,s1),s)) = 
      (List.map (fn x => (x,y,s1)) l)@(nonarities s) 
  | nonarities (Bind_sc(_,s)) = (nonarities s);

(* observe we replace `nonarities' with `binders' in thetazero *)

fun nthetazero S z = (* 2011: List.foldr *) 
  let 
    val l1 = (* nonarities *) binders S;      (* Conor's alteration *)
      val (name,ty) = get_name_and_type S;
    val l2 = arities S
  in (* 2011: List.foldr *) 
    let val begin = List.foldr 
      (fn ((str,x,schema),z) =>
        mkPiExp_c x Local [str^"_ih"] (nphizero schema (ref_c(str))) z)
      (nstart_up S z name ty)
      l2
    in (* 2011: List.foldr *) 
      List.foldr (fn ((name,x,cnstr),z) => mkPiExp_c x Local [name] cnstr z)
      begin
      l1
    end 
  end;
		    
fun neliminator schema_names name type_of_name list_of_schemas typestr =
    let val name_l = binders_ind type_of_name;
	val start_value = nUniver_of_C name_l name;
	val innerpart = (* 2011: List.foldr *) 
	  (List.foldr 
	   (fn ((str,schema),z) => mkPiExp_c Vis Local [""] (nthetazero schema str) z)
	   start_value 
	   list_of_schemas)
    in (* 2011: List.foldr *) 
      List.foldr 
      (fn ((str,cnstr),z) => 
      	   mkPiExp_c Vis Local ["C_"^str] (nT_of_C (binders_ind cnstr) str typestr) z)
      innerpart
      schema_names
    end;

fun neliminators schema_names list_of_schemas typestr =
  List.map (fn (str,cnstr) => 
       (Prefix(Lda,Vis,UnFroz,Global,[]),[str^"_elim"],
	(neliminator schema_names str cnstr list_of_schemas typestr))(*:binder_c*))
  schema_names;
  
(* Need to elaborate ``schema_names'' so as to retain the
   type information from which derives type of ``C'' *)

(* Need something to force an argument into every Pi binding
   in a schema else create one... *)

fun nfirst_bindings name_list typestr = 
   List.map (fn (str,cnstr) => 
    (Prefix(Lda,Vis,UnFroz,Local,[]),["C_"^str],
     (nT_of_C (binders_ind cnstr) str typestr))(*:binder_c*)) name_list;

fun nsecond_bindings schema_list =
    List.map (fn (str,schema) =>  
    (Prefix(Lda,Vis,UnFroz,Local,[]),[mkNameGbl("f_"^str)], 
     (nthetazero schema str))(*:binder_c*))
    schema_list;

fun nall_bindings name_list schema_list typestr =
   (nfirst_bindings name_list typestr) @ (nsecond_bindings schema_list) @
   (third_bindings schema_list);

(* takes a constructor name and its schema and gives back
   what Luo calls ``\iota(bar{a})'', a cnstr_c '' *)

(* Should have eliminated the rev by using foldl...check this ! *)


fun nrecursor_applied_to_bindings name_list schema_list (x,S) = (* 2011: List.foldl *)
  let val (str,ty) = get_name_and_type S
  in
     (List.foldl (fn ((name,schema),cnstr)
			  => (mkApp_c(cnstr,ref_c(mkNameGbl("f_"^name))))) 
      (List.foldl (fn ((name,cnstr2),cnstr) =>
			   (mkApp_c(cnstr,ref_c("C_"^name))))
       (ref_c((str)^"_elim")) name_list)
      schema_list)
  end;

(* Instead, we rip off the reductions from the non-Relation types,
   (source in ind_relations.sml) and insert the odd judicious `n' *)

fun nlhs_of_reduction name_list schema_list (x,S) =
  mkApp_c(
(* the absence of the app_of_schema_applied removes the explicit
   parameter names no longer wanted since Conor hid them         *)  
	(recursor_applied_to_bindings name_list schema_list (x,S)),
	(iota_of_a(x,S)));

(* the hack of nphihash above does the same for the rhs *)
(* observe also the `binders' where there was a `nonarities' *)
fun nrhs_of_reduction name_list schema_list (x,S) = (* 2011: List.foldl *)
  List.foldl 
  (fn ((name,y,schema),cnstr) =>
    app_c((prVis y),cnstr,(nphihash schema   
			   (recursor_applied_to_bindings
			    name_list schema_list (name,schema))
			   (ref_c(name))))) 
  (List.foldl
   (fn ((name,y,cnstr2),cnstr) =>
     (app_c((prVis y),cnstr,(ref_c(name)))))
   (ref_c(mkNameGbl("f_"^x))) (binders S))
  (arities S);

(* ie the above are almost the non-Rel reductions *)

fun nmake_reductions name_list schema_list typestr=
     red_c(mkCtxt (nall_bindings name_list schema_list typestr),
   (List.map (fn (x,S) => 
     ((nlhs_of_reduction name_list schema_list (x,S)),
      (nrhs_of_reduction name_list schema_list (x,S))))
    schema_list));
    

fun do_weak_inductive_type (safe:bool) (with_bindings)
                      (declaration_bindings)
                      (schema_bindings)
                      (is_relation:bool) 
                      (typestr:cnstr_c) = 
  let
    val with_bindings = unCtxt with_bindings
    val declaration_bindings = unCtxt declaration_bindings
    val schema_bindings = unCtxt schema_bindings
    val init_context = redo_bindings_with_dependency safe with_bindings
                                                     declaration_bindings
				                     schema_bindings
    val schema_list =
      nice_schemas (make_schema_list declaration_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list declaration_bindings schema_bindings
    val _ = ((fn ("TYPE") => () | _ => raise Match) (* 2011: catch "TYPE" *)
    	     (Concrete.getRefNam typestr)
	     ) handle _ => (* Match from fn, Concrete.getConcrete from getRefnam *)
	         message "Your value for ElimOver is ignored in defining a relation \n"
  in
    (mkCtxt(init_context @ (neliminators name_list schema_list typestr)),
     (if is_relation then (prop_c) 
      else (nmake_reductions name_list disj_sch_list typestr)))
 end;

(* double.sml *)

fun mapply l c = (* 2011: List.foldl *)
    List.foldl 
    (fn ((nam,v,_),so_far) => (app_c((prVis v),so_far,ref_c(nam))))
    c
    l;
    
fun mapply_var l c = (* 2011: List.foldl *)
    List.foldl 
    (fn ((nam,v,_),so_far) => (app_c((prVis v),so_far,ref_c(nam^"_f"))))
    c
    l;

(* 2011 version *)
fun new_binders_ind v_c = 
   let
      val ((Prefix(_,d,_,_,_),l,s1),s) = Concrete.getBinder v_c
   in 
      (List.map (fn x => (x,d,s1)) l)@(new_binders_ind s)
   end handle getConcrete => [];
  
(* 1998 version *
fun new_binders_ind (Concrete.Bind_c((_,d,_,_,l,s1),s)) = 
      (List.map (fn x => (x,d,s1)) l)@(new_binders_ind s)
  | new_binders_ind (_) = [];
 *)
					      
fun dashify x = x^"'";
fun dashify_list l = List.map dashify l;
fun dashify_binds l = List.map (fn (x,y,z) => (dashify x,y,z)) l;    

fun is_dash str = List.hd (List.rev (String.explode str)) = #"'";
(*    last (explode str) = #"'"; (* 2011: to avoid last, removeLast etc. *) *)
    
fun iota_prime_of_a (x,S) = (* 2011: List.foldl *) 
   List.foldl
   (fn ((nam,v,_),cnstr) => (app_c((prVis v),cnstr,ref_c(dashify nam))))
   (ref_c(x)) 
   (binders S);
fun start_up_special S z T_applied = 
     mkApp_c(T_applied,(iota_prime_of_a (z,S)));

    
(* 2011 version *)
fun dashify_inside_binds str v_c = 
   let
      val ((pfx,l1,c1),c2) = Concrete.getBinder v_c
   in 
      if (is_dash (hd l1)) then
       (bind_c((pfx,l1,(subst_c (str,dashify str) c1)),
         (dashify_inside_binds str c2))) 
       else v_c 
   end handle getConcrete => v_c;
  
(* 1998 version *
fun dashify_inside_binds str (Concrete.Bind_c((x,y,c,d,l1,c1),c2))
      = if (is_dash (hd l1)) then
       (bind_c((x,y,c,d,l1,(subst_c (str,str^"'") c1)),
         (dashify_inside_binds str c2))) 
       else (bind_c((x,y,c,d,l1,c1),c2)) |
      dashify_inside_binds str constr = constr;
 *)

fun dashify_inside_list l c1 =
    List.foldr(fn (str,rest) => dashify_inside_binds str rest)
    c1 l;
    
fun dashify_subst l c1 =
    List.foldr(fn ((str,_,_),rest) => subst_c (str,dashify str) rest) c1 l;


fun phizero_T T_app (Ref_s(s)) z l1 = mkApp_c(T_app,z)
  | phizero_T T_app (Bind_s((Prefix(Pi,x,_,_,_),l,c),c1)) z l1 =
                     mkPiExp_c x Local (dashify_list l) (dashify_subst l1 c)  
    (dashify_inside_list l (phizero_T T_app  c1 (gen_app z x (dashify_list l)) l1))
  | phizero_T _ _ z _ = raise sch_err "Schema is not strictly positive";

fun theta_end S z S1 z1 =
  let 
    val l1 = binders S1
    val (name,ty) = get_name_and_type S1
    val l2 = arities S1
    val T_app = mkApp_c(ref_c("T_"^name),(iota_of_a (z,S)))
  in (* 2011: List.foldr *)
    let val begin = List.foldr 
      (fn ((str,x,schema),z) =>
       (mkPiExp_c x Local [str^"_ih"] (phizero_T T_app schema (ref_c(dashify str)) l1) z))
      (start_up_special S1 z1 T_app)
      l2
    in 
      List.foldr 
      (fn ((name,x,cnstr),so_far) =>
       (mkPiExp_c x Local [dashify name] cnstr (dashify_inside_binds name so_far)))
      begin
      l1
    end 
  end;

fun phizero_ext T_qunt (Ref_s(s)) z = T_qunt z
  | phizero_ext T_qunt  (Bind_s((Prefix(Pi,x,_,_,_),l,c),c1)) z =
       mkPiExp_c x Local l c (phizero_ext T_qunt  c1 (gen_app z x l))
  | phizero_ext _ _ z = raise sch_err "Schema is not strictly positive";

(* This is wrong !!!! *)

fun theta_rest dname dtype S z S1 z1 =
  let 
    val l1 = binders S;
    val l2 = arities S;
    val lnames = new_binders_ind dtype   
    fun T_qunt x =  
      List.foldr (fn ((a,_,b),x) => mkPiExp_c Hid Local [a] b x)
(*** Need to pi-bind also by binders in schema head ***)
     (mkPiExp_c Vis Local ["z"] (mapply lnames (ref_c(dname)))
             (mkApp_c(mkApp_c(ref_c("T_"^dname),x),ref_c("z"))))
      lnames
  in (* 2011: List.foldr *)
    let val begin = List.foldr 
      (fn ((str,x,schema),z) =>
       (mkPiExp_c x Local [str^"_ih"] (phizero_ext T_qunt schema (ref_c(str)))) z)
      (theta_end S z S1 z1)
      l2
    in 
      List.foldr (fn ((name,x,cnstr),z) => mkPiExp_c x Local [name] cnstr z)
      begin
      l1
    end 
  end;

fun make_theta_abstr dname dtype  S z S1 z1 =
  (Prefix(Lda,Vis,UnFroz,Local,[]),[z^"_"^z1^"_case"],
        (theta_rest dname dtype S z S1 z1)) (*:binder_c;*)

fun make_all_theta dname dtype schemalist start = (* 2011: List.foldr *)
    List.foldr
         (fn ((str,schem),rest) =>
           (List.foldr 
             (fn ((newstr,newschem),newrest) =>
             bind_c(make_theta_abstr dname dtype  schem str newschem newstr,newrest))
            rest
            schemalist)
          )
         start
         schemalist;
	 

(* Here we need to  also pi bind by implict args to schema head *)
fun do_elim_rule name type_of_name =
   let val l1 = dashify_binds (new_binders_ind type_of_name)
            in
   mkApp_c(ref_c(name^"_elim"),
   (List.foldr (fn ((a,_,b),x) => mkLdaExp_c Hid Local [a] b x)
    (mkLdaExp_c Vis Local ["z"] (mapply l1 (ref_c(name))) 
    (List.foldr (fn ((a,_,b),x) => mkPiExp_c Hid Local [a] b x)
      (mkPiExp_c Vis Local ["z'"] (mapply l1 (ref_c(name)))
         (mkApp_c(mkApp_c(ref_c("T_"^name),ref_c("z")),ref_c("z'"))))
        l1))
      l1))
   end;

fun do_inside_elim_head name nametype S z =  
   let val l1 = new_binders_ind nametype in
 mkApp_c(ref_c(name^"_elim"),
  (List.foldr (fn ((a,_,b),x) => mkLdaExp_c Hid Local [a] (dashify_subst l1 b) x)
      (mkLdaExp_c Vis Local ["z"] (mapply (dashify_binds l1) (ref_c(name))) 
      (mkApp_c((mkApp_c(ref_c("T_"^name),iota_of_a (z,S))),ref_c("z"))))
      (dashify_binds l1))
 ) end ;
 

fun applied_theta z z1 arities binders =
    mapply_var arities (mapply binders (ref_c(z^"_"^z1^"_case")));
    
fun phi_zero_inside_part (Ref_s(s)) z = z
  | phi_zero_inside_part (Bind_s((Prefix(Pi,x,_,_,_),l,c),c1)) z =
                 (phi_zero_inside_part c1 (gen_app z x l))
  | phi_zero_inside_part _ z = raise sch_err "Schema is not strictly positive";

fun phi_zero_outside (Ref_s(s)) start = start 
  | phi_zero_outside  (Bind_s((Prefix(Pi,x,_,_,_),l,c),c1)) z =
       mkPiExp_c x Local l c (phi_zero_outside c1 z)
  | phi_zero_outside  _ z = raise sch_err "Schema is not strictly positive";

(* Again need to pi-bind by binders of dname *)
fun approp_T str schem dname dtype =
     let val lname = new_binders_ind dtype in 
     phi_zero_outside schem
        (List.foldr (fn ((a,_,b),x) => mkPiExp_c Hid Local [a] b x)
      (mkPiExp_c Vis Local ["z"] (mapply lname (ref_c(dname)))
	     (mkApp_c((mkApp_c(ref_c("T_"^dname),
      (phi_zero_inside_part schem  (ref_c(str))))),
		   ref_c("z"))))
        lname
) end;

(* Must change the above function to also do a phizero
   like-trick....first change ''str'' to be a schema. *)

fun make_whole_second_elim dname nametype S z schema_list = 
    let val l1 = binders S;
	val l2 = arities S;
        val start = (* 2011: List.foldl *)
            List.foldl 
            (fn ((name,schma),cnstr) => 
                  mkApp_c(cnstr,(applied_theta z name l2 l1)))
            (do_inside_elim_head dname nametype S z)
            schema_list
    in (* 2011: List.foldr *)
      List.foldr  
      (fn ((name1,vsrt,typ),z) => mkLdaExp_c vsrt Local [name1] typ z)
      (List.foldr 
       (fn ((name,vsrt,schme),z) =>
        mkLdaExp_c vsrt Local [name^"_f"] (approp_T name schme dname nametype) z)
       start
       l2)
      l1
    end;
    
fun make_all_elims schema_list dname d_type = (* 2011: List.foldl *)
    List.foldl
    (fn ((z,S),cnstr) =>
         mkApp_c(cnstr,(make_whole_second_elim dname d_type S z schema_list)
     ))
    (do_elim_rule dname d_type)
    schema_list;

(*
fun double_T_of_C l str typestr = 
  List.foldr (fn ((a,b,_),x) => Bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x))
   (Bind_c((Pi,Vis,(UnFroz,Local),[],[""],(start_T_of_C (dashify_binds l) str)),
  (Bind_c((Pi,Vis,(UnFroz,Local),[],[""],(start_T_of_C l str)),typestr))))
   (l @ (dashify_binds l)) 
;
 
*)

local  

   fun pi_bind ((a,b,_),x) = mkPiExp_c Hid Local [a] b x
in 

   fun double_T_of_C l str typestr = 
      List.foldr pi_bind
        (mkPiExp_c Vis Local [""] (start_T_of_C l str) 
 	   (List.foldr pi_bind
   	      (mkPiExp_c Vis Local [""] (start_T_of_C (dashify_binds l) str) typestr)
   	      (dashify_binds l)
   	    )
	)
   l  
end;

(*
The above new version of this function which will correct strange order of
arguments in double elim rule!
*)


fun do_all schemalist dname d_type all_dnames typestr = (* 2011: List.foldr *)
    List.foldr 
    (fn ((str,cnstr),z) =>
     mkLdaExp_c Vis Local ["T_"^dname] (double_T_of_C (binders_ind cnstr) str typestr) z)
    (make_all_theta dname d_type schemalist (make_all_elims schemalist dname d_type))
    all_dnames
;
        
fun add_it schemalist [(dname,d_type)] typestr =  
    [(Prefix(Let,Def,UnFroz,Global,[]),[dname^"_double_elim"],
        (do_all schemalist dname d_type [(dname,d_type)] typestr ))] |
    add_it schemalist all_dnames typestr =
    (prs("Double elimination not implemented for mutual recursion \n");
    []);


(* The whole thing is......
   First lambda abstract by T,
   then by theta_rest applied to each possible pair of schemas
   
   now first elim, applied to T with first arg lambda abstracted
       and 2nd arg universally quantified.... 
                [z:intype]{z':indtype}T z z'
   now for each constructor we have a further nat-elim, applied
   to T partially instantiated with iota for that constructor
   and then applied to appropriate theta-rests....
   the nat_elim is lambda abstracted by each binder and arity and then
   each arity, the theta-rests are instantiated with these bindings *)

fun do_inductive_type_double (safe:bool) (with_bindings(*ctxt_c*))  
                      (declaration_bindings(*ctxt_c*))
                      (schema_bindings(*ctxt_c*))
                      (is_relation:bool)
		      (typestr:cnstr_c) = 
  let
    val _ = message "** prove double elim rule **"
    val with_bindings = unCtxt with_bindings
    val declaration_bindings = unCtxt declaration_bindings
    val schema_bindings = unCtxt schema_bindings
    val init_context = redo_bindings_with_dependency safe with_bindings
                                                     declaration_bindings
				                     schema_bindings
    val schema_list =
      nice_schemas (make_schema_list declaration_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list declaration_bindings schema_bindings
    val (dn,dT) = hd name_list
  in
    (pr_cc (do_all schema_list (dn) (dT) name_list typestr));
    (mkCtxt(init_context @ (eliminators name_list schema_list typestr)
     			 @ (add_it disj_sch_list name_list typestr)),
(* Only change is above here, schema_list replaced by disj_sch_list *)
     (if is_relation then (prop_c) 
      else (make_reductions name_list disj_sch_list typestr)))
 end;


(* Works fine on nat and list *)
(* Need to change for: mutual recursion.....*not* properly handled yet,
   also check handling of inductive relations *)

(* theorems.sml *)

	    val H = Utils.StringUtil.HYPNAME

val absurd = ref_c("absurd");
    
val negate = ref_c("not");
    
val identy = ref_c("Id");
    
val legotrue = mkApp_c(negate,absurd);
    
val proof_of_legotrue = mkAppNoShow_c(identy,absurd);
    
fun blank_to_prop name = mkLdaExp_c Vis Global [""] (ref_c(name)) prop_c;

val equlty = ref_c("Eq")
val eqrefl = ref_c("Eq_refl")
val eqresp = ref_c("Eq_resp")
val eqrefl = ref_c("Eq_refl")
val eqsbst = ref_c("Eq_subst")

fun get_name schema = #1 (get_name_and_type schema);
    


fun phizero_prime t1 (Ref_s(s)) = t1
  | phizero_prime t1 (Bind_s((Prefix(Pi,x,_,_,_),l,c),c1)) =
                     mkPiExp_c x Local [""] c (phizero_prime t1 c1)  
  | phizero_prime t1 _ = raise sch_err 
                       "Schema is not strictly positive";


fun all_pi_something S t t1 = (* S is a schema, t,t1 are constr_c *)
     let val l1 = binders S;
	 val (name,ty) = get_name_and_type S;
	 val l2 = arities S
     in
	 let val begin = List.foldr 
		  (fn ((str,x,schema),z) => 
		     mkLdaExp_c x Global [""] (phizero_prime t1 schema) 
		     z)
             t l2
         in 
	     List.foldr (fn ((name,x,cnstr),z) => 
	     	       mkLdaExp_c x Global [""] cnstr 
	     	      z) begin l1
         end 
  end;

fun bind_by_list ([]) init = init
  | bind_by_list ((a,x,y)::l) init = 
    bind_by_list l (mkPiExp_c x Local [a] y init);
    

fun equality_part_only (n,S1) (m,S2) =
  mkApp_c(mkApp_c(equlty,iota_of_a (n,S1)),iota_of_a (m,S2));
  
fun construct_theorem (n,S1) (m,S2) = 
  bind_by_list ((binders S1)@(binders S2))
  (mkApp_c(negate,(equality_part_only (n,S1) (m,S2))));
  
fun lambda_bind_by_list ([]) init = init
  | lambda_bind_by_list ((a,x,y)::l) init = 
    lambda_bind_by_list l (mkLdaExp_c x Local [a] y init);
  
(* Supposed to construct the type of the theorem that
   the binders n and m are distinct... *)

(* This appears to do the right thing on a simple case now.... *)


(* Now a function to construct the proof term !! *)

(* 2011: List.foldl *)
fun make_up_jj datatype_name name_list list_of_schemas_and_names (n:string,S1) =
   List.foldl 
    (fn ((cons_name,schema),concrete) =>
    let val new_term = 
          if cons_name = n 
             then   (all_pi_something schema legotrue (prop_c))
             else  (all_pi_something schema absurd (prop_c))
    in (mkApp_c(concrete,new_term))
    end  )
   (List.foldl 
    (fn ((other_name,_),so_far) => 
    	mkApp_c(so_far,blank_to_prop other_name))
    (ref_c(datatype_name^"_elim"))
    name_list
    ) 
    list_of_schemas_and_names;


fun whole_proof_term datatype_name name_list list_of_schemas_and_names (n,S1) (m,S2)
= 
lambda_bind_by_list ((binders S1)@(binders S2))
(mkLdaExp_c Vis Global [H] (equality_part_only (n,S1) (m,S2))
  (mkApp_c(
   (mkApp_c(
    (mkApp_c(eqsbst,ref_c(H))),
    (make_up_jj datatype_name name_list list_of_schemas_and_names (n,S1)))),
	(mkAppNoShow_c(identy,absurd)))));



fun make_cast datatype_name name_list list_of_schemas_and_names (n,S1) (m,S2) =
  cast_c(
    (whole_proof_term datatype_name name_list 
          list_of_schemas_and_names (n,S1) (m,S2)),
	 (construct_theorem (n,S1) (m,S2)));

fun make_all_disjointness_theorems name_list schemas 
    			   []              = []
  | make_all_disjointness_theorems name_list schemas 
             ((name,schema)::rest_of_list) =
    let val datatype_name = get_name schema in
    List.foldr 
    (fn ((new_name,new_schema),theorems_so_far) =>
            if ((get_name new_schema)=datatype_name) 
               then (name,new_name,(make_cast datatype_name name_list schemas
                     (name,schema) (new_name,new_schema)))::theorems_so_far
            else theorems_so_far)
    (make_all_disjointness_theorems name_list schemas rest_of_list)
    rest_of_list
    end;
    
(* To actually give these theorems.... *)

(* Now work on constructor injectivity *)

fun make_identity_fun S (string,_,var_ty)  = 
     (* S is a schema, string is a binder name in S  *)
     let val l1 = binders S;
	 val (name,ty) = get_name_and_type S;
	 val l2 = arities S
     in (* 2011: List.foldr *)
	let val begin = List.foldr 
		  (fn ((str,x,schema),z) => 
		     mkLdaExp_c x Global [""] (phizero_prime var_ty schema) z)
             (ref_c(string)) l2
        in 
	     List.foldr 
	     (fn ((name,x,cnstr),z) => mkLdaExp_c x Global [name] cnstr 
	     	     z) begin l1
        end 
  end;

fun blank_to_type name = mkLdaExp_c Vis Global [""] (ref_c(name)) ;

(* 2011: List.foldl *)
fun make_up_kk datatype_name name_list list_of_schemas_and_names 
    (n:string,S1) (var_name,_,var_type) =
   List.foldl 
    (fn ((cons_name,schema),concrete) =>
    let val new_term = 
          if cons_name =n 
             then   (make_identity_fun schema (var_name,1,var_type))
             else  (all_pi_something schema (ref_c(var_name^"1")) var_type)
    in (mkApp_c(concrete,new_term))
    end  )
   (List.foldl 
    (fn ((other_name,_),so_far) => 
       mkApp_c(so_far,blank_to_type other_name var_type))
    (ref_c(datatype_name^"_elim"))
    name_list
    )
    list_of_schemas_and_names;

fun bind_by_list_funny name ([]) init = init
  | bind_by_list_funny name ((a,x,y)::l) init = 
    (* if a=name then  *)
    bind_by_list_funny name l (mkPiExp_c x Local [a^"1",a^"2"] y init)
    (* else bind_by_list_funny name l (Bind_c((Pi,x,(UnFroz,Local),[],[a],y),init))  *);

(* changed to make theorem correct *)
(* This won't work if there are dependencies in the schema parameters...
   I don't even know if you *can* prove the injectiveness...nor
   does Thorsten !! *)
(*
fun new_iota_of_a string1 string2 (x,S) = (* 2011: List.foldl *)
   List.foldl
   (fn ((name,x,cnstr2),cnstr) =>
    if name=string1 then (app_c((prVis x),cnstr,ref_c(string2)))
       else (app_c((prVis x),cnstr,ref_c(name))
                )
   )
   (ref_c(x)) 
   (binders S);   


fun equality_part_only_2 (n,S) var_name  =
  mkApp_c(mkApp_c(equlty,
     (new_iota_of_a var_name (var_name^"1") (n,S))),
     (new_iota_of_a var_name (var_name^"2") (n,S)));

New versions of these functions follow.
*)


fun new_iota_of_a string1 (x,S) = (* 2011: List.foldl *)
    List.foldl
    (fn ((name,x,cnstr2),cnstr) =>
     (app_c((prVis x),cnstr,ref_c(name^string1)))
        )
    (ref_c(x)) 
    (binders S);
 
 fun equality_part_only_2 (n,S) var_name  =
   mkApp_c(mkApp_c(equlty,
      (new_iota_of_a "1" (n,S))),
      (new_iota_of_a "2" (n,S)));

fun construct_theorem_2 (n,S) (var_name,_,_) =
  bind_by_list_funny  var_name (binders S) 
(mkPiExp_c Vis Local [""] (equality_part_only_2 (n,S) var_name) 
 (mkApp_c(mkApp_c(equlty,
		      ref_c(var_name^"1")),ref_c(var_name^"2"))));

    
fun lambda_bind_by_list_funny name ([]) init = init
  | lambda_bind_by_list_funny name ((a,x,y)::l) init = 
    (* if a=name then  *)
    lambda_bind_by_list_funny name l (mkLdaExp_c x Local [a^"1",a^"2"] y init)
    (*  else lambda_bind_by_list_funny name l 
       (Bind_c((Lda,x,(UnFroz,Local),[],[a],y),init))    *);
  (* Changed to make theorem correct *)

fun func_type datatype_name = 
   mkPiExp_c Vis Local [""] (ref_c(datatype_name))
(* 
    Bind_c((Pi,Vis,(UnFroz,Local),[],[""],ref_c(datatype_name)),var_type);
 *)
 
fun whole_proof_term_2 datatype_name name_list 
  list_of_schemas_and_names (n,S1) (var_name,x,var_type) =
lambda_bind_by_list_funny var_name (binders S1)
(mkLdaExp_c Vis Global [H] (equality_part_only_2 (n,S1) var_name)
   (mkApp_c(
    (mkApp_c(eqresp,
(cast_c((make_up_kk datatype_name name_list list_of_schemas_and_names (n,S1)
	   (var_name,x,var_type)),(func_type datatype_name var_type))))),
	   ref_c(H))));

fun make_cast_2 
datatype_name name_list list_of_schemas_and_names (n,S1) 
(var_name,_,var_type) =
  cast_c(
    (whole_proof_term_2 datatype_name name_list 
          list_of_schemas_and_names (n,S1) (var_name,1,var_type)),
	 (construct_theorem_2 (n,S1) (var_name,1,var_type)));

(* Copied from below *)
fun make_all_inj_theorems name_list schemas [] =
     []
|   make_all_inj_theorems name_list schemas 
             ((name,schema)::rest_of_list) =
    let val datatype_name = get_name schema 
        val list_of_binders = binders schema
in (* 2011: List.foldr *)
    List.foldr 
    (fn ((var_name,vsort,var_type),theorems_so_far) =>
               (name,var_name,(make_cast_2 datatype_name name_list schemas
                  (name,schema) (var_name,vsort,var_type)))::theorems_so_far)
    (make_all_inj_theorems name_list schemas rest_of_list)
    list_of_binders
    end;
    
(* To actually give these theorems.... *)

(* Now think about theorem that every term is constructed from
   the constructors *)


(* First part we need to construct is a schema, for each binder,
   an existential quantification ... *)

fun make_exists str typ const =
  mkApp_c(ref_c("Ex"),mkLdaExp_c Vis Local [str] typ const);
  

fun do_existentials S constructor = (* 2011: List.foldr *)
    List.foldr 
    (fn ((str,_,cons),typ) =>
            make_exists (str^"_ex") cons typ)
    constructor
    (binders S);
    
fun another_iota_of_a (x,S) = (* 2011: List.foldl *)
   List.foldl
   (fn ((name,x,cnstr2),cnstr) =>
     (app_c((prVis x),cnstr,ref_c(name^"_ex"))
                )
   )
   (ref_c(x)) 
   (binders S);


fun appropriate_equality (x,S) sch_new =
    mkApp_c(
         (mkApp_c(equlty,sch_new)),
	 (another_iota_of_a (x,S)));
    
fun part_of_theorem (x,S) new_sch =
    do_existentials S (appropriate_equality (x,S) new_sch);

fun or_these_together constr1 constr2 =
    mkApp_c(mkApp_c(ref_c("or"),constr1),constr2);
    
fun pick_out_right_schemas list_of_schema dtname
    = filter_pos (fn (n,S) => (dtname=get_name S)) list_of_schema;
    
fun all_ors_on_theorem [(n,S)] new_name dtname =
        (part_of_theorem (n,S) (ref_c(new_name)))
|   all_ors_on_theorem ((n,S)::list_of_schema) new_name dtname =
    (or_these_together (part_of_theorem (n,S) (ref_c(new_name)))
       (all_ors_on_theorem list_of_schema new_name dtname))
|   all_ors_on_theorem _ new_name dtname =
    bug ("No appropriate schemas found for datatype "^dtname);
	
fun real_theorem list_of_schema datatype_name =
  mkPiExp_c Vis Local [(datatype_name^"_var")] (ref_c(datatype_name))
   (all_ors_on_theorem 
      (pick_out_right_schemas list_of_schema datatype_name)
      (datatype_name^"_var") datatype_name)
   ;
  

(* Theorem is checked now ... *)

(* Now for proof.... *)


(* 2011: List.foldl *)
fun elim_rule_applied_to_prop list_of_schema datatype_name datatype_list  =
   List.foldl
   (fn ((name,_),so_far) =>
    if (name=datatype_name)
    then mkApp_c(so_far,
           mkLdaExp_c Vis Local [(datatype_name^"_var")]
		   (ref_c(datatype_name))
   (all_ors_on_theorem 
        (pick_out_right_schemas list_of_schema datatype_name)
        (datatype_name^"_var") datatype_name)
     )
   else 
         mkApp_c(so_far,
		mkLdaExp_c Vis Local [""] (ref_c(name)) legotrue)
     )
   (ref_c(datatype_name^"_elim"))
   datatype_list;

(* very much like the theorem *)

(*
fun mem_left x ((a,b)::l) = (a = x) orelse mem_left x l
  | mem_left x       []   = false
 *) 
  
fun more_new_iota_of_a lofvar (x,S) = (* 2011: List.foldl *)
   List.foldl
   (fn ((name,x,cnstr2),cnstr) =>
    if (mem_assoc name lofvar) then (app_c((prVis x),cnstr,ref_c(name^"1")))
       else (app_c((prVis x),cnstr,ref_c(name))
                )
   )
   (ref_c(x)) 
   (binders S);

fun make_eq_refl_term (x,S) =
    mkApp_c(eqrefl,(iota_of_a (x,S)));
    

fun make_equality_term (x,S) changed_vars =
    mkApp_c(
         (mkApp_c(equlty,iota_of_a (x,S))),
	 (more_new_iota_of_a changed_vars (x,S)));

(* changed vars is the list of variables whose names are to be
   changed to the primed form *)
(*
fun make_exists_intro str typ const =
  mkApp_c(exintros_of_old_type,
	Bind_c((Lda,Vis,(UnFroz,Local),[],[str],typ),const));
*)


fun make_exists_intro str typ const =
  mkApp_c(mkLift_c(ref_c("ExIntro")),
	mkLdaExp_c Vis Local [str] typ const);


(* 2011: List.foldr *)
fun do_next_intros (x,S) new_var new_type changed_vars_list = 
    make_exists_intro (new_var^"1") new_type
  (List.foldr 
   (fn ((a,ty),(constrc:cnstr_c))  =>
        (make_exists (a^"1") ty constrc))
  (make_equality_term (x,S) ((new_var,new_type)::changed_vars_list))
   changed_vars_list
  );
  
fun do_all_intros (x,S) init = (* 2011: List.foldr *)
    List.foldr
    (fn ((str,_,typ),(so_far,l)) =>
          (mkApp_c((do_next_intros (x,S) str typ l),so_far)
         ,((str,typ)::l))
        )
   (init,[])
   (binders S);
    
fun all_ex_intros (x,S) =
    let val (out,_) = do_all_intros (x,S) (make_eq_refl_term (x,S))
    in out end;
	
fun apply_inr cn (n,S) (n1,S1) =
    mkApp_c(
          mkAppNoShow_c(ref_c("inr"),
                (part_of_theorem (n,S) (iota_of_a (n1,S1))))
          ,cn);

fun pick_out_right_schemas_funny list_of_schema dtname
   = filter_pos (fn ((n,S),_) => (dtname=get_name S)) list_of_schema;
   
fun new_all_ors_on dname [((n,S),_)] new_cn  =
        (part_of_theorem (n,S) (new_cn))
|   new_all_ors_on dname (((n,S),_)::list_of_schema) new_cn =
    (or_these_together (part_of_theorem (n,S) (new_cn))
       (new_all_ors_on dname list_of_schema new_cn))
|   new_all_ors_on dname _ new_cn =
    bug ("No appropriate schemas found for datatype"^dname);

fun apply_inl dname cn (n,S) funny_list =
    mkApp_c(
          mkAppNoShow_c((mkAppNoShow_c(ref_c("inl"),mkNewVar_c)), (* no LiftNoShow! *)
                (new_all_ors_on dname 
      (pick_out_right_schemas_funny funny_list dname) (iota_of_a (n,S))))
          ,cn); 

fun map_inr_to_appro dname (n,S) list_of_stuff =
    List.map (fn ((n1,S1),x) => 
     if (dname = get_name S1) then 
        ((n1,S1),apply_inr x (n,S) (n1,S1))
        else ((n1,S1),x))
	    (list_of_stuff);
	    
fun do_apply count dname stuff_so_far (n,S) =
    if (count=0) then 
        ((((n,S),(all_ex_intros (n,S)))::stuff_so_far),1)
           else 
       ((((n,S),(apply_inl dname 
		 (all_ex_intros (n,S)) (n,S) stuff_so_far))::
	 (map_inr_to_appro dname (n,S) stuff_so_far)),count);
       

fun all_ins_on_theorem dtname schema_list = (* 2011: List.foldr *)
   List.foldr   
   (fn ((x,S),(so_far,n)) =>
      if (dtname=get_name S)
         then
           (do_apply n dtname so_far (x,S))
         else ((((x,S),proof_of_legotrue)::so_far),n))
   ([],0)
   schema_list;
   

fun outer_abstractions1 (n,S) list_of_schema name cn1 =
   let val sch_list = arities S     
   in (* 2011: List.foldr *)
      List.foldr
      (fn ((str,v,sch),z)  => 
      	  mkLdaExp_c v Global [""] 
            (if (name=get_name sch) then
             (bind_by_list (binders sch)
	     (all_ors_on_theorem 
               (pick_out_right_schemas list_of_schema name)
	       str name)
            )
            else (legotrue)
            )
	z)

          (* fn so_far =>
            Bind_c((Lda,v,(UnFroz,Global),[],[""],
            (if (name=get_name sch) then
             (bind_by_list (binders sch)
	     (all_ors_on_theorem 
               (pick_out_right_schemas list_of_schema name)
	       str name)
            )
            else (legotrue)
            )),so_far) *)
      cn1
      sch_list
   end;
   
fun outer_abstractions2 (n,S) list_of_schema name cn1 =
    lambda_bind_by_list (List.rev (binders S))
    (outer_abstractions1 (n,S) list_of_schema name cn1);

fun abstract_on_ins list_of_schema name  =
    List.map
    (fn ((n,S),cn1) => 
     outer_abstractions2 (n,S) list_of_schema name cn1) 
    (#1 (all_ins_on_theorem name list_of_schema));
     
(* 2011: List.foldl *)
fun whole_ex_theorem list_of_schema datatype_name dtype_list =
    List.foldl
    (fn (cn,so_far) => mkApp_c(so_far,cn))
    (elim_rule_applied_to_prop list_of_schema datatype_name dtype_list)
    (abstract_on_ins list_of_schema datatype_name);
    
(* Now think about the or's.... *)
(* The first schema is always inl with sucessive schemas
   an extra  inr ?... *)

fun make_ex_cast list_of_schema datatype_name dtype_list =
  cast_c((whole_ex_theorem list_of_schema datatype_name dtype_list),
         (real_theorem list_of_schema datatype_name));
  
fun list_all_ex_theorem list_of_schema dtype_list = 
   (List.map
   (fn (name,_) => 
    (Prefix(Let,Def,UnFroz,Global,[]),[name^"_char"],
	    (make_ex_cast list_of_schema name dtype_list)))
   dtype_list);

fun list_all_dis_theorems name_list schema_list =
    let val list_of_thms =  make_all_disjointness_theorems name_list
	                   schema_list schema_list
    in
    (List.map
       (fn (name1,name2,cast) => 
          (Prefix(Let,Def,UnFroz,Global,[]),[name1^"_not_Eq_"^name2],cast))
     list_of_thms)
    end;

fun list_inj_theorems name_list schema_list =
    let val list_of_thms =  make_all_inj_theorems name_list
	                   schema_list schema_list
    in
     (List.map    
       (fn (name1,name2,cast) => 
          (Prefix(Let,Def,UnFroz,Global,[]),[name1^"_is_inj_"^name2],cast))
      list_of_thms)
    end;

fun list_all_theorems sch_list dtype_list =
    ((list_all_dis_theorems dtype_list sch_list)@
    (list_inj_theorems dtype_list sch_list)@
   (list_all_ex_theorem  sch_list dtype_list));

fun do_inductive_type_with_theorems (safe:bool) (with_bindings)
                      (declaration_bindings)
                      (schema_bindings) (is_relation:bool) 
                       (typestr:cnstr_c)
                       = 
  let
    val init_context = redo_bindings_with_dependency safe with_bindings
                                                     declaration_bindings
				                     schema_bindings
    val schema_list =
      nice_schemas (make_schema_list declaration_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list declaration_bindings schema_bindings
  in
    ((init_context @ (eliminators name_list schema_list typestr)),
  (make_reductions name_list disj_sch_list),
   (list_all_theorems disj_sch_list name_list)
    )
end;

fun do_just_theorems (with_bindings)
                      (declaration_bindings)
                      (schema_bindings) 
                       = 
  let
    val declaration_bindings = unCtxt declaration_bindings
    val schema_bindings = unCtxt schema_bindings
    val schema_list =
      nice_schemas (make_schema_list declaration_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list declaration_bindings schema_bindings
  in
    mkCtxt (list_all_theorems disj_sch_list name_list)
end;

(* record.sml *)

(* 2011 version *)
fun subst_l l v_c = Concrete.subForRef l v_c
    handle Concrete.getConcrete => raise sch_err "Metavariables not allowed here"
         | Concrete.errConcrete => raise sch_err "error in subst_l";
  
fun make_into_single_constr ([]) name = ref_c(name) 
  | make_into_single_constr ((Prefix(Lda,b,UnFroz,Local,[]),l,cn)::lis) name 
  = mkPiExp_c Vis Global l cn (make_into_single_constr lis name)
  | make_into_single_constr _ name = raise sch_err "Invalid record type";
    

fun phizero_prime t1 (Ref_s(s)) = t1
  | phizero_prime t1 (Bind_s((Prefix(Pi,x,_,_,_),l,c),c1)) 
  = mkPiExp_c x Local [""] c (phizero_prime t1 c1)  
  | phizero_prime t1 _ = raise sch_err 
                       "Schema is not strictly positive";

fun make_identity_fun S (string,_,var_ty)  = (* 2011: List.foldr *)
     (* S is a schema, string is a binder name in S  *)
     let val l1 = binders S;
	 val (name,ty) = get_name_and_type S;
	 val l2 = arities S
     in
	let 
	   val begin = List.foldr (* 2011: List.foldr *)
	   (fn ((str,x,schema),z) => 
	       mkLdaExp_c x Global [""] (phizero_prime var_ty schema) z)
           (ref_c(string)) 
	   l2
        in 
	   List.foldr (* 2011: List.foldr *)
	   (fn ((name,x,cnstr),z) => 
	       mkLdaExp_c x Global [name] cnstr z) 
	   begin 
	   l1
        end 
  end;


fun subst_list [] c name = c |
    subst_list (a::l) c name =
      subst_l (a,(mkApp_c(ref_c(a),ref_c(name^"_var"))))
      (subst_list l c name);

fun get_x_to_type name names_done ty =
    mkLdaExp_c Vis Global [name^"_var"] (ref_c(name))
     (subst_list names_done ty name);


fun make_function S (string,_,var_ty) name names_done =
    ((Prefix(Let,Def,UnFroz,Global,[]),[string],
    (mkApp_c((mkApp_c(ref_c(name^"_elim"), 
       (get_x_to_type name names_done var_ty))),
	   (make_identity_fun S (string,1,var_ty))))));
    

fun make_all_recs_aux name schema stuff [] = [] |
    make_all_recs_aux name schema stuff ((var_name,vsort,var_type)::l)
    =
   (make_function schema (var_name,vsort,var_type) name stuff) 
   :: (make_all_recs_aux name schema (var_name::stuff) l);
   
fun make_all_records name schema =
    let val list_of_binders = binders schema
in
    make_all_recs_aux name schema []
    list_of_binders
    end;

fun do_record_type (params) (decl_bindings) 
    (record_bindings) (typestr:cnstr_c) =
  let
    val params = unCtxt params
    val decl_bindings = unCtxt decl_bindings 
    val record_bindings = unCtxt record_bindings 
    val name = hd (get_names decl_bindings)
    val schema_bindings = [(Prefix(Lda,Vis,UnFroz,Global,[]),["make_"^name],
		  (make_into_single_constr record_bindings name))]
    val init_context = redo_bindings_with_dependency false params
                                                     decl_bindings
				                     schema_bindings
    val schema_list =
    nice_schemas (make_schema_list decl_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list decl_bindings schema_bindings
    val (_,S) = hd schema_list
  in
    (mkCtxt(init_context @ (eliminators name_list schema_list typestr)),
     (make_reductions name_list disj_sch_list typestr),
     mkCtxt(make_all_records name S))
 end;



 end (* local *) 

end; (* struct *)
