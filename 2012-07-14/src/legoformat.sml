(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* format_words sl separates the words in sl by a space                *)
(* format pretty_print_mode exp_flg formats a lego expression. If      *)
(* exp-flg then the expression will be expanded                        *)
(* legoformat = format false followed by a linefeed                    *)
(* format_expand = format explicit followed by a linefeed              *)
(* format_goal will format an unexpanded current goal                  *)
(* format_vt (v,t) will format a value and a type, separated by a colon*)
(* format_vt_expand will do the same but expand, both value and type   *)
(* format_red will format a reduction (without expanding)              *)
(* format_decl will format a declaration                               *)
(* format_cannot_assume id (v,t) will print an error message             
                                 if v is of type t and t is not a kind *)
(* format_value uses legoformat to format a value                      *)
(* format_type  uses legoformat fo format a type                       *)
(* format_refine g v uses legoformat to format the value v which has 
                     has refined goal g                                *)
(* format_bind b will print the definition of b in the context         *)

(* format_defn will format a definition: uses formatInteractive        *)
(* format_goals will format toplevel proof state: uses formatInteractive        *)

(* print prints a formatted block (from Format)                        *)
 

functor FunLegoFormat (
	structure Term:TERM
	) 
(* *** * 
structure LegoFormat 
 * *** *)
	: LEGOFORMAT 
 = 
struct

	type cnstr   = Term.cnstr 
   	type binding = Term.binding 
   	type visSort = Term.visSort 

	val legoprompt = "Lego> "

	val bug = Utils.Except.bug

  datatype granularity = explicit | implicit 
    	     		 | tuples (* explicit, but non-dependent tuples 
			     	     will have no typing information *) 


  val notImplicit = fn implicit => false | _ => true
  val  isExplicit = fn explicit => true  | _ => false

  datatype dfnsPrnt = OmitDfns | ElideDfns | ShowDfns | Marks 


(* ******************** pulled from Format ********************* *)
  local
     (* open Format *)
  in 

    type block = Format.block

    val newline = Format.linebreak
    val string = Format.string
    val block = Format.block
    val block0 = Format.block0
    val break = Format.break
    val postlf = Format.postlf

    val print = Format.print

    fun add_myint i = string (Int.toString i)
    val emptyblock = string Utils.StringUtil.nullString

    fun prompt os = print os (string (Annotate.promptAnnotating legoprompt)) (* **** *)
    
    val formatInteractive = Format.formatInteractive
    val formatAnnotating = Format.formatAnnotating
    val path_wrap = Format.path_wrap (* This is still a bit of a hack *)

    val SetLineWidth = Format.SetLineLength
    fun isPrettyPrinting _ = (!Format.active)
    fun SetPrettyPrinting isActive  = Format.active:=isActive

    val _ = SetPrettyPrinting true (* ************************** *)
    val _ = Format.indent := 0

    fun AvoidPrettyPrinting f x =
      let val active = isPrettyPrinting()
      in  (if active then SetPrettyPrinting false else ();
	   f x;
	   SetPrettyPrinting active)
      end

    val prnso = print TextIO.stdOut

  end (* of local open Format *)
(* ************************************************************* *)

  local
      fun t2s2 b [] = "!)"
        | t2s2 b (h::t) = (if b then "(!" else " ")^h^(t2s2 false t)
  in  fun tag2string [] = "(! !)"
        | tag2string x = t2s2 true x
  end

  fun bb l r m = block0 [string l, m, string r] 
  val square = bb "[" "]"
  val parens = bb "(" ")" 
  val curly = bb "{" "}"
  val pointed = bb "<" ">"
  val expBr = bb "<*" "*>"  (* show expansion *);

  fun relates R l r = [l, string R, r]
  val colon = relates ":"
  val gencolon = relates " : " (* generous colon *)

  (* format existential variables n |-> ?n *)
  fun format_mvar n = block0 [string "?", add_myint n]

(* A concrete syntax for pretty-printing *)

local

     open Term

in 

  val whnfr = ref (fn (c:cnstr) => c) (* set to whnf function *)

  datatype prCnstr = PrBot
    | PrProp
    | PrType  of Universes.node
    | PrRef   of string
    | PrRel   of int
    | PrApp   of prCnstr * ((prCnstr * prntVisSort) list)
    | PrBind  of string list * bindVisSort * prCnstr * prCnstr
    | PrVar   of int * prCnstr
    | PrTuple of prCnstr * (prCnstr list)
    | PrProj  of projSort * prCnstr
    | PrRedTyp of instrs * prCnstr
    | PrThry
    | Pr_theory of (string * prCnstr * prCnstr) list
    | PrCast of (string list * bindVisSort * prCnstr) list * prCnstr * prCnstr
          (* rewrite  reductions  *)
    | PrRedBod of (prCnstr * prCnstr) list  (* rewriting reductions *)
  ;

  fun prSpine l = #1 (ListPair.unzip l)

  exception getPrCnstr

  fun getPrPi (PrBind(id_list, (Pi,Vis), A, B)) = (id_list, A, B)
    | getPrPi _ = raise getPrCnstr

  fun mkPrPi (id_list, A, B) = PrBind(id_list, (Pi,Vis), A, B)

  fun getPrArr (PrBind([], (Pi,Vis), A, B)) = (A, B)
    | getPrArr _ = raise getPrCnstr

  fun mkPrArr (A, B) = PrBind([], (Pi,Vis), A, B)

  fun getPrLet (PrBind(id_list, (Let,_), A, B)) = (id_list, A, B)
    | getPrLet _ = raise getPrCnstr

  fun mkPrLet (id_list, A, B) = PrBind(id_list, (Let,Def), A, B)

(* need a "samePrCnstr" for the polyEqual test below *)

  val bindSym =
    fn Vis => ":" | Hid => "|" | Def => "=" | VBot => bug"bindSym"

  val visSym =
    fn Vis => ":" | _ => "|" 

  val hidSym =
    fn Hid => "|" | _ => ":" 

  val builtinInfixSym =
    fn Pi => "->" | Sig => "#"    (* | Lda => "\\" *)
     | _ => ""                    (** "" means no infix; force var  **)

  val projSym = fn Fst => ".1" | Snd => ".2" | Labl(s) => "^"^s

(* format for printing *)
  fun ffp granularity isRed = 
    let
      val exp_flg = notImplicit granularity 

      fun ffpef c =
	case c of
	  Var(x,c) => PrVar(exvar_index x,(if exp_flg then ffpef c else PrBot))
	| Prop     => PrProp
	| Theory   => PrThry
	| Type(i)  => PrType(i)
	| Ref(br)  => PrRef (case ref_kind br
                             of  (GenTag tag) => tag2string tag
                              | 	_     => ref_nam br)
	| Rel(n)   => PrRel(n)
	| App((c,gs),vs) => 
	  let
	    val vs =
	      if exp_flg then List.map (fn NoShow => ShowExp | v => v) vs
	      else if List.all (fn v => v=NoShow) vs
		     then List.map (fn NoShow => ShowForce | v => v) vs
		   else vs
	    fun ap ((c,NoShow),gvs) = gvs
	      | ap ((c,pv),gvs)     = (ffpef c,pv)::gvs
	  in  PrApp(ffpef c,List.foldr ap [] (ListPair.zipEq (gs,vs))) (* zipEq *)
	  end
	| Bind((Thry,_),_,_,CnLst bs) =>
	  let fun aux (LabVT(Name s,v,t)) = (s,ffpef v,ffpef t)
		| aux _ = bug"ffpef:theory"
	  in  Pr_theory (List.map aux bs)
	  end
	| Bind(bv,s,c,d) => ffp_binder bv s c d
	| Tuple(T,ls)    => ffp_tuple T ls
	| Proj(p,c)      => PrProj(p,ffpef c)
	| LabVT(_,v,t)   => PrCast([],ffpef v,ffpef t)   (** temp **)
	| RedTyp(i,c)    => PrRedTyp(i,ffpef c)
	| CnLst cs       => if isRed then ffp_red cs
			      else bug"ffpef;CnLst"
	| Bot            => PrBot
	| _		 => bug"ffpef: Match failure!"

      and ffp_binder (bv as (bind,_)) s c1 c2 =
	let
	  val showVar = (exp_flg andalso s<>"") orelse var_occur c2
	  val _ = if showVar andalso s="" then bug"ffp_binder"
		  else ()
	  val forceVar = (not showVar) andalso (builtinInfixSym bind = "")
	  val s = Utils.StringUtil.wildcard_ forceVar s
	in
	  case (showVar orelse forceVar,ffpef c2)
	    of (false,x) => PrBind([],bv,ffpef c1,x)
	     | (true,(inr as PrBind((ls as (_::_)),bv',c,x))) =>
		 if bv=bv' andalso (c = (ffpef (lift (length ls) c1))) (* polyEqual *)
		   then PrBind(s::ls,bv,c,x)
		 else PrBind([s],bv,ffpef c1,inr)
	     | (true,x) => PrBind([s],bv,ffpef c1,x)
	end
      and ffp_tuple T ls =
	let
	  fun isDepTpl (T,[_]) = false
	    | isDepTpl (T,_::ls) =
	      (case (!whnfr) T (* sole use of whnf! *) 
		 of Bind((Sig,_),_,_,tr) =>
		      var_occur tr orelse isDepTpl (tr,ls)
		  | _ => bug"isDepTpl1" )
	    | isDepTpl _ = bug"isDepTpl2"
	  val T = if (isExplicit granularity) orelse isDepTpl(T,ls)
		    then ffpef T
		  else PrBot
	  in  PrTuple(T,List.map ffpef ls)
	end
     and ffp_red ls =
       let fun mkPrRedBod [] = []
	     | mkPrRedBod (LabVT(RedPr,c1,c2)::cs) =
	         (ffpef c1,ffpef c2)::(mkPrRedBod cs)
	     | mkPrRedBod _ = bug"ffp_red"
       in  PrRedBod (mkPrRedBod ls)
       end

(* ************************* *
and ffp_sharCast (V,T) =
     let 
       fun pre_sC (PrV,PrT) =
	 case (PrV,PrT)
	       of (PrBind(ns,bv as (b,v),pc,pd),
		 PrBind(ns',(b',v'),pc',pd')) =>
		 if ((b=Let andalso b'=Let) orelse (b=Lda andalso b'=Pi))
		   andalso ns=ns' andalso v=v' andalso pc=pc'
                     then case pre_sC (pd,pd')
			    of PrCast(front,pl,pr) =>
			         PrCast((ns,bv,pc)::front,pl,pr)
			     | _ => bug"pre_sC"
                     else PrCast([],PrV,PrT)
	         | _ => PrCast([],PrV,PrT)
	  in pre_sC (ffpef V,ffpef T)
	  end
 * ************************ *)

    in ffpef
    end;

  val ffp_pbp = ffp implicit false 

(* put a numeric extension on a print-name if the current binder is in the
 * scope of another binder with the same print-name, or there is a reference
 * to global with the same print name in the scope of the current binder
 *)
local

  fun okLoc s = (Utils.StringUtil.isNullString s) orelse (Utils.StringUtil.isWILDCARD s) 

  fun okGlb prc s = 
    let
      fun pro (PrRef(nam))      = s = nam
	| pro  PrProp           = false
	| pro  PrThry           = false
	| pro (Pr_theory _)     = false   (****************)
	| pro (PrType(_))       = false
	| pro (PrVar(_,t))      = pro t
	| pro (PrRel(_))        = false
	| pro (PrApp(c,l))      = (pro c) orelse (List.exists pro (prSpine l))
	| pro (PrBind(_,_,c,d)) = (pro c) orelse (pro d)
	| pro (PrTuple(T,ls))   = (pro T) orelse (List.exists pro ls)
	| pro (PrProj(_,c))     = pro c
	| pro (PrRedTyp(_,c))   = pro c
	| pro (PrCast(ls,c,T))  = (pro c) orelse (pro T)  (******)
	| pro (PrRedBod(ccs))   = List.exists (fn (c,d) => pro c orelse pro d) ccs
	| pro  PrBot            = false
    in 
       not (pro prc)
    end

in 

  fun add_name s nams prc = Utils.StringUtil.fresh_push okLoc (okGlb prc) s nams 

end;

local 

      val nth = Utils.ListUtil.nth
      exception Nth = Utils.ListUtil.Nth

      val nameIsInfix = Infix.nameIsInfix 

      val infix_data = Infix.infix_data 
      val infix_sym  = Infix.infix_sym  

      fun nAssoc str = (Infix.NAssoc,str)
      fun lAssoc str = (Infix.LAssoc,str)
      fun rAssoc str = (Infix.RAssoc,str)

      val noNAssoc = nAssoc "no" 

      val isNAssoc = fn Infix.NAssoc => true | _ => false 
      val isLAssoc = fn Infix.LAssoc => true | _ => false 
in 

  fun format_ granularity isRed nams c =
    let

      val exp_flg = notImplicit granularity

(* 2011: tried to move to universe.sml * 
      (* format_univ_levl:node -> block *)
      fun format_univ_levl (Uvar(Named(s),_)) = parens (string s)
	| format_univ_levl (Uconst(n)) 	      = parens (add_myint n)
	| format_univ_levl (Uvar(Unnamed(n),_)) = emptyblock
 * *********************************** *)


      fun formatProp () = (case Theories.theory() 
			      of Theories.lf => string "Type"
			       | _  	     => string "Prop")

      fun format_node format_type nod = Universes.nodeCase format_type 
      	  	      		    (fn s => block0 [string "Type",parens (string s)])
				    (fn n => block0 [string "Type",parens (add_myint n)])
				       nod
			       
      fun formatType nod = (case Theories.theory()
		  	       of Theories.lf => string "Kind"
		   	        | _  => format_node (string "(Type)") nod )
		     		     	(* parenthesis are needed due  *
		     		 	 * to LEGO's ambiguous grammar *)

      val bracket =
	fn Pi => curly
	 | Lda => square
	 | Sig => pointed
	 | Let => square
	 | Thry => bug"format_:bracket";

(* ******************** path_wrap pushed into Format ********************* *

      fun path_wrap l ls = 
	  if isAnnotating () then 
	      (annotate (rev l))::(ls@[annotate [252]])
	  else ls 
      (* This is a bit of a hack: the 250 and 251 codes will be added
         in the prettyprinting module when path-compression happens.
	 Format.sml *)

 * *********************************************************************** *)

      fun fr_rec path names c = 
	case c
	  of PrRef(nam)  => string nam
	   | PrProp      => formatProp () 
	   | PrThry => string "Theory"
	   | Pr_theory bs => 
	       string("theory["^Utils.StringUtil.concat_comma (List.map #1 bs)^"]")
	   | PrType(nod) => formatType nod 
	   | PrVar(n,t) =>
	       if exp_flg then expBr (pr_exp_Var path names n t)
	       else format_mvar n
	   | PrRel(n) =>
	       (string (nth names n)  
		handle Nth _ =>  (** in case of open subterm **)
		  (expBr (block0 [string "Rel ",
				   add_myint n])))
	   | PrApp(b) => parens (fr_app noNAssoc path names b) 
(* 
                (case b of (PrRef(x),[n1,n2]) => 
                   if nameIsInfix x 
		       then fr_infix path names noNAssoc x n1 n2
		   else fr_apps path names b
   	         | _ => fr_apps path names b)
 *)
	   | PrBind(l,bv,c3,c4) => 
	       parens (block0 (fr_binder path names (bv,c3,c4) l))
	   | PrTuple(b) => parens (pr_tuple path names b)
	   | PrProj(s,c) =>
	       block0 [(case c
			   of PrRef(_)  => fr_rec path names c
			    | PrRel(_)  => fr_rec path names c
			    | PrProj(_) => fr_rec path names c
			    | _         => parens (fr_rec path names c)),
			string (projSym s)]
	   | PrRedTyp(i,c) =>
	       parens (block0 (string"NormTyp "::fr_outer_rec path names c))
	   | PrCast(b) => parens (pr_cast path names b)
	   | PrRedBod(ccs) => fr_red_bod path names ccs
	   | PrBot     => string Utils.StringUtil.WILDCARD


      and fr_app ii path names b = 
      	 (case b 
	  of (PrRef(x),[n1,n2]) => if nameIsInfix x 
		    then fr_infix path names ii x n1 n2
		else fr_apps path names b
      	   | _ => fr_apps path names b)

      and fr_outer_rec path names c = 
	(* some outermost parens not needed; otherwise fr_outer_rec
	 * does the same as fr_rec
	 *)
	case c of
	  PrBind(l,bv,c3,c4) => fr_binder path names (bv,c3,c4) l
	| PrApp(b) => [fr_app noNAssoc path names b]
(* 
             (case b of (PrRef(x),[n1,n2]) => 
                if nameIsInfix x 
		    then [fr_infix path names (NAssoc,"no") x n1 n2]
		else [fr_apps path names b]
              | _ => [fr_apps path names b])
 *)
(* 	| PrType(Uvar(Unnamed _,_)) => [string "Type"] (* is it right now? *) *)
	| x as PrType(nod) 	    => [Universes.nodeCase (string "Type") 
	       			        (fn _ => fr_rec path names x)
	       			        (fn _ => fr_rec path names x)
	       			        nod]
	| x              => [fr_rec path names x]

      and fr_infix_rec path names ii b =
         (case (b,ii) of 
            (PrApp(app as (PrRef(x),[n1,n2])),_) => 
             if nameIsInfix x then [fr_infix path names ii x n1 n2]
  	                        else [fr_apps path names app]
	  | (PrBind((_::_),_,_,_),(assoc,_)) => 
	      if isLAssoc assoc
	      	 then (string "(")::(fr_outer_rec path names b)@[string ")"]
	      else (fr_outer_rec path names b)
 	  |  _ => fr_outer_rec path names b)

      and fr_apps path names (c,args) =
	let fun prarg path =
	  let fun SMtoString ShowNorm = " "
		| SMtoString ShowForce = "|"
		| SMtoString ShowExp = "%%"
		| SMtoString _ = (bug "fr_apps";"")
	  in fn (c,ShowMode) => 
	     	(string (SMtoString ShowMode))::
		((path_wrap path [(fr_rec path names c)])@[break 0])
	  end
	in let fun argloop n p [] = []
		 | argloop n p (a::l) =  (prarg (n::p) a)::((argloop (n+1) p l))
	   in block0 ((path_wrap (1::path) [fr_rec (1::path) names c])@
		       (List.concat (argloop 1 (2::path) args)))
	   end
	end
	
      and fr_infix path names (branch, par) nam (a1,_) (a2,_) =
          let val sym = infix_sym nam in 
	      let val arg1 = path_wrap (1::2::path) 
		   	(fr_infix_rec (1::2::path) names (lAssoc sym) a1)
		  val arg2 = path_wrap (2::2::path) 
		      	(fr_infix_rec (2::2::path) names (rAssoc sym) a2)
	      in let val txt = 
		  block0 (arg1@
			  ((break 1)::(path_wrap (1::path) [string sym]))@
			  ((break 1)::arg2))
		 in if isNAssoc branch  
		       then if par = "no" then txt else parens txt
		    else if par = sym
				then if branch = #1 (infix_data sym)
					 then txt else parens txt
			    else if #2 (infix_data nam) > #2 (infix_data par)
				     then txt else parens txt
		 end
	      end
          end 

      and fr_binder path names ((b,v),c,d) l =
	let 
	  fun pbr n p (nams:string list) ls =
	    case ls
	      of []   => bug "fr_binder"
               | [l]  => let val (name, scope) = add_name l nams d
                           in (block0 (path_wrap (n::p) [string name]),scope)
			 end
	       | (l::ls) =>
		   let val (name,scope) = add_name l nams d
		     val (name',scope') = pbr (n+1) p scope ls
		   in  (block0 ((path_wrap (n::p) [string name])
				 @[string ",", name']), scope')
		   end
	in 
	  case l
	    of [] => let val (_,scope) = add_name "" names PrBot
		     in  (path_wrap (1::2::path) [fr_rec (1::2::path) names c])
			@(path_wrap (1::path) [string(builtinInfixSym b)])@
	                 [break 0]@
			  (path_wrap (2::2::path) (fr_infix_rec (2::2::path)
						   scope (nAssoc "yes") d))
		     end
	     | ls => let val (name,scope) = pbr 1 (1::path) names ls
                         val l1 = (path_wrap (1::path) [name])
	                 val l2 = path_wrap (2::path) 
					(fr_outer_rec (2::path) (tl scope) c)
                         val l3 = path_wrap (3::path)
				   (fr_infix_rec (3::path) scope (nAssoc "") d)
                         in (bracket b 
	                       (block0 (l1@((string (bindSym v))::l2))))::
	                    ((break 0)::l3)
		     end
	end

      and pr_exp_Var path names n t =
	block0 (colon (format_mvar n) (fr_rec path names t))

      and pr_tuple path names (T,ls) = 
	let
	  fun mapcolon f [] = []
	    | mapcolon f [x] = [f x]
	    | mapcolon f (h::t) = f h::string ","::mapcolon f t
	in
	  block0 ((mapcolon (block0 o (fr_outer_rec path names)) ls) @
		   (case T 
		      of PrBot => []
		       | _     => string ":" :: fr_outer_rec path names T
		    )
		  )
	end

      and pr_cast path names (ls,c,T) =  (********************)
	block0 (colon (block0 (fr_outer_rec path names c))
		 (block0 (fr_outer_rec path names T)))
		
      and fr_red_bod path names ccs =
	let 
	  fun prb (c1,c2) = block0 [(block0 (fr_outer_rec path names c1)),
				     break 2,
				     string "==>",
				       break 2,
				       (block0 (fr_outer_rec path names c2))]

	  fun PRB (cc::[]) = [prb cc]
	    | PRB (cc::ccs) = prb cc             ::
	      break 0      ::
	      string "|| " ::
	      PRB ccs
	    | PRB [] = [emptyblock]
	in 
	  block0 (string "   " :: PRB ccs)
	end
	    
    in (* here appears path_wrap from annotation.sml *)

      path_wrap [] (fr_outer_rec [] nams (ffp granularity isRed c))

    end (* of let defining format_ *)

end (* of local open Infix *)

(* ******************** push into Format ********************* *
  fun formatAnnotating bl = if isAnnotating() then string "\253" else bl
 * ******************** push into Format ********************* *)

(* (* 2011: to avoid dropLast *)
  val format_words =
    dropLast o List.concat o List.map (fn s => [string s, break 1]) 
 *)

  val format_red_ = format_ implicit true []

  val format_red = postlf o square o block0 o format_red_ (* format_ implicit true [] *)

  val format_cnstr_ = fn  true => format_ explicit false []
      		       | false => format_ implicit false []

  fun format_cnstr b = block0 o (format_cnstr_ b)

  val format = format_cnstr false (* formerly format implicit *)

  val legoformat = postlf o format
			
  val format_expand_ = format_cnstr_ true (* format_ explicit false [] *) 

  val format_expand = postlf o (format_cnstr true) (* block0 o format_expand_ *) 

  val format_tuples_ = format_ tuples false []

  val format_tuples = block0 o format_tuples_ 

  fun format_vt (v,t) = block0 (gencolon (format v) (legoformat t)) 
      		       (* block0 (format_ implicit false [] v) *)


  fun format_vt_expand (v,t) = 
    postlf (block0 (gencolon (block0 (format_expand_ v))
		     (block0 (format_expand_ t))))

  fun format_words   []    = []
    | format_words (s::ss) = ((string s)::(List.concat 
      	     (List.map (fn s => [break 1, string s]) ss)));

  fun format_decl v id t =
    block (8, (format_words ["decl ", id, visSym v]) @  (* *** visSym, or bindSym *** *)
	   [break 1, legoformat t])


  fun format_cannot_assume id (vt as (v,t)) =
    block (2, [string "cannot assume", break 1,
	       string id, break 1,
	       string ":", break 1] @
	   (format_expand_ v) @
	   [break 1,
	    string ":", break 1,
	    format_expand t])

  fun format_value "" v = block (2, (format_words ["value", "="]) @
				 [break 1, format v])

    | format_value id v = block (2, (format_words ["value", "of", id, "="]) @
				 [break 1, format v])

  fun format_type "" v = block (2, (format_words ["type ", "="]) @
				[break 1, format v])
    | format_type id v = block (2, (format_words ["type ", "of", id, "="]) @
				[break 1, format v])
  fun format_refine g v =
    block (2, [string "Refine", break 1] @
	   (if g>0 then [add_myint g, break 1] else []) @
	      [string "by", break 2,
	       legoformat v])

(* *** format_bind and format_goal check isAnnotating *** *)
local
(* 2011: aaaargh! caused by my lack of understanding of mutual types in SML *)

  fun format_binding _ _ (Mrk (module,imports,_,_)) _
    = postlf (block (5, format_words (" ** Module" :: module ::
				      (case imports of
					 [] => []
				       | _  => "Imports" :: imports))))

    | format_binding Marks _ _ _          
      = emptyblock

    | format_binding _ _ (Red) (_,_,v,_)
      = postlf (format_red v)

    | format_binding _ _ (Config (a,(b,c,d))) _ 
      = postlf (block (4, format_words [" ** Config",a,b,c,d]))

    | format_binding _ _ (LabelTag (tag,name)) _ 
      = postlf (block (4, format_words [" ** Label",tag2string tag,name]))

    | format_binding OmitDfns _ _ ((Let,_),_,_,_) 
      = emptyblock

    | format_binding elideFlg br K ((Let,_),id,v,t)
      = postlf (block (4, [if (ref_isFrozen br) then string "*" else break 1,
			     if (ref_isLocal br) then string "$" else break 1,
                               case K
                                 of GenTag tag =>
                                    string (" Gen "^(tag2string tag)^" as ")
                                  | _ => break 0,
			       formatAnnotating (break 0),  (* *** *)
			       string id, break 1,
			       string "=", break 1,
			       if elideFlg=ElideDfns then (string "...")
			       else (format v),
				 break 1, string ":", break 1,
				 format t]))

    | format_binding _ br _ ((_,vis),id,v,_)
      = postlf (block (4, [break 1,
			   if (ref_isGlobal br) then string "$"
			   else break 1, 
			     formatAnnotating (break 0),  (* *** *)
			     string id, break 1, 
			     string (hidSym vis), (* *** hidSym, or bindSym *** *)
			     break 1, format v]))
in 

   fun format_bind flag (br) = format_binding flag br (ref_kind br) (ref_bd br)

end;

  fun format_goal (n,c)
    = postlf (block (2, [string "  ", formatAnnotating (string " "), (* *** *)
			 block0 (gencolon (format_mvar n) 
			 		  (format c) 
				  (* block0 (format_ implicit false [] c) *)
				  )
			]))
	
(* *** format_goals and format_defn check isInteractive *** *)

  val format_goals = List.concat o (List.map (fn g => formatInteractive [format_goal g] []))

  fun format_defn id v t = formatInteractive (* *** *) 
      [(block (2, [string "defn", break 2] @ 
			    (format_words [id,"="]) @
			    [break 1, legoformat v])) , 
	      (block (2, (break 6) ::
			    (format_words [id,":"]) @
			    [break 1, legoformat t]))] 
	 
       [block (8, (format_words ["defn ",id,"=","...",":"]) @
			 [break 1,legoformat t])]
	
end (* of local open Term *)

end; (* of structure LegoFormat *)		   

(*
structure LegoFormat = FunLegoFormat (structure Infix = Infix);
(* open LegoFormat; needed for the grammar and for Namespace? tidy up *)
 *)

