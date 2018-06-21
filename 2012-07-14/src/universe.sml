(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* universe.ml *)
(* Author: Randy Pollack <pollack@cs.chalmers.se> *)

(* CHANGES 

   Thomas Schreiber <tms@lfcs.ed.ac.uk>

   1994
   removed the function print_univ_levl, 
   pretty printing is now handled by the module Pretty 

   February 1995
   added ImpredicativeSums, predicativeSums
   to incorporate small impredicative \Sigma-types 
*)

(* "mode" operations are placed here because they must be first *)

structure Theories : THEORIES 
 = 
struct
	val message = Printing.message

val TypeType  = ref false
and LuosMode  = ref true
and AczelMode = ref true;

fun PredicativeSums b = (AczelMode:=b; 
    		      	 if b 
			 then
                           message"strong predicative Sigma-types"
			 else
			   message"small impredicative Sigma-types")
and TypesStratified() = (TypeType:= false; message"Types Stratified")
and TypeInType()      = (TypeType:= true; message"Type in Type");

datatype theories = lf | pureCC | xtndCC;

val prThy = fn lf => "LF" | pureCC => "PCC" | xtndCC => "XCC"

local 
      val inference = ref(xtndCC,false) 
in fun set_inference (t,e) = (inference := (t,e))
   and theory _ = #1 (!inference)
   and eta _ = #2 (!inference)
end;

val LF = (lf,true)
and LF_no_n = (lf,false)
and PCC = (pureCC,false)
and PCC_n = (pureCC,true)
and XCC = (xtndCC,false)
and XCC_n = (xtndCC,true);

fun ThytoString () = prThy (theory ())

fun init_theories() = message ((case theory()
		     of lf     => "LF"
		      | xtndCC => "Extended CC"
		      | pureCC => "Pure CC")
		      ^": Initial State!")

end;

(* *********************************************************************** *)

structure Universes : UNIVERSES 
 = 
struct 

	val prs = Printing.prs
	val pri = Printing.pri
	val prnl = Printing.prnl

	val ASSOC = Utils.ListUtil.ASSOC
	val assoc = Utils.ListUtil.assoc
	val mem_assoc = Utils.ListUtil.mem_assoc
	val member = Utils.ListUtil.member

	val succ = Utils.Counting.succ

	val bug = Utils.Except.bug

(* *********************************************************************** *
This is not a satisfactory implementation.  The graph is stored as a list,
with new info added to the front of the list.  Thus the state of the graph
may be rolled back when unification backtracks.
 * *********************************************************************** *)

datatype node_lim = Num of int | Infinity
datatype label = Unnamed of int | Named of string
type node_body = int * node_lim * (label list) * (label list)
         (*      min ,   max ,       gt_list ,     ge_list  *)
type labeled_node_body = label * node_body

datatype node = Uvar of labeled_node_body | Uconst of int
datatype univ_cnstrnt = UniGe of node | UniGt of node
type univ_graph = labeled_node_body list;

(****** for debugging ***********)
local
  val prNL = fn Num(n) => pri n | Infinity => prs"^"
  val prLab = fn (Unnamed n) => (pri n;prs",") | (Named s) => prs(s^",")
  fun prLst lst = (prs" ["; List.map prLab lst; prs"]") (* List.app *)
in
  val prNode =
    fn Uconst(n) => (prs"T";pri n)
     | Uvar(Unnamed n,(min,max,gt,ge)) => 
	 (prs"V";pri n;prs"  ";pri min;prs"-";prNL max;prLst gt;prLst ge)
     | Uvar(Named s,(min,max,gt,ge)) => 
	 (prs"V";prs s;prs"  ";pri min;prs"-";prNL max;prLst gt;prLst ge)
end;
(*********************************)

(* a hack to minimise sharing constraints with legoformat *)

fun nodeCase unnamed unamed uconst nod = 
    case nod 
      of (Uvar(Unnamed(n),_)) => unnamed
       | (Uvar(Named(s),_))   => unamed s
       | (Uconst(n)) 	      => uconst n 

val NodetoString1 = nodeCase "(Type)"
    		    	      (fn s => "Type("^s^")")
			      (fn n => "Type("^(Int.toString n)^")") 

val NodetoString2 = nodeCase "Type"
    		    	      (fn s => "Type("^s^")")
			      (fn n => "Type("^(Int.toString n)^")") 

(* *** *
      (* format_univ_levl:node -> block *)
      fun format_univ_levl (Uvar(Named(s),_)) = parens (string s)
	| format_univ_levl (Uconst(n)) 	      = parens (add_myint n)
	| format_univ_levl (Uvar(Unnamed(n),_)) = emptyblock

fun format_nod nod = case nod 
    	       	       of (Uvar(Unnamed(n),_)) => string "(Type)"
		     	   	      (* parenthesis are needed due to * 
		      	    	       * LEGO's ambiguous grammar      *)
		     	|  _ => block0 [string "Type",
				     	format_univ_levl nod]
 * *** *)

fun nodLim_gt m (Num(n)) = m > n 
  | nodLim_gt m Infinity = false;

fun mkNod f u0 u1 u2 (Uconst(0)) = u0
  | mkNod f u0 u1 u2 (Uconst(1)) = u1
  | mkNod f u0 u1 u2 (Uconst(2)) = u2
  | mkNod f u0 u1 u2   nod       = f nod

local   
  val Uconst0 = Uconst 0
  val Uconst1 = Uconst 1
  val Uconst2 = Uconst 2
in
  fun mkUcon 0 = Uconst0     (* optimize storage *)
    | mkUcon 1 = Uconst1
    | mkUcon 2 = Uconst2
    | mkUcon j = Uconst j
end;

fun node_equal (Uvar(k,_)) (Uvar(l,_)) = k=l
  | node_equal (Uconst(m)) (Uconst(n)) = m=n
  | node_equal _ _                     = false;

exception Universes of string;

  val UVARS = ref ([]:univ_graph) (* *** namespace.sml, unif.sml, Umachine.sml, *** *)

local

  (* open LegoUtils *)

  val NBR_UVARS = ref 0

  val UVARS_HIST = ref [!UVARS]

  fun pushUniverse () = let 
      		      	    val uvars = !UVARS
			    val uvars_hist = !UVARS_HIST
      		      	in 
			    UVARS_HIST := uvars :: uvars_hist
			end 

  fun popUniverse () = let 
      		       	   val (u::us) = !UVARS_HIST
			   val _ = UVARS:= u
			   val _ = UVARS_HIST:= us
      		       in 
		       	  ()
		       end handle Match => raise Universes "no more history!"

  val CYCLE = "cycle"
  val LIMIT = "constant limits headroom"
  val CLASH = "constants clash"

  fun thrd (_, _, z) = z; 

  fun fnd_nod (Uvar(i,_)) nods = (Uvar(ASSOC i nods) handle _ => bug"fnd_nod")
    | fnd_nod (nod as Uconst(_)) nods = nod;

  fun propagate (ii,Mnan as (M,n,an)) = (* 2011: List.foldl *)
    (if M > !NBR_UVARS then raise Universes CYCLE else ();
     let val (imin,imax,gt,ge) = ((assoc ii an)
				  handle _ => bug"propagate:assoc")
     in if imin >= n then Mnan              (* i already >= j*)
	else if nodLim_gt n imax 
	       then raise Universes LIMIT
	     else let val an = (ii,(n,imax,gt,ge))::an     
                                       (* make i >= j, and propagate *)
		  in List.foldl propagate 
		    (M+1,n,thrd(List.foldl propagate (M+1,n+1,an) gt)) ge 
		  end 
     end); 

  fun add_cnstr kk (UniGe j,an) = (* 2011: List.foldl *)
    if node_equal kk j then an 
    else
      (case (fnd_nod j an,kk)
	 of (Uvar(jj,(jmin,jmax,gt,ge)),Uvar(ii,_))
	    => if (member ii ge) orelse (member ii gt) then an
	       else thrd(propagate 
			 (ii,(0,jmin,(jj,(jmin,jmax,gt,ii::ge))::an)))
	  | (Uconst n,Uconst m)
	    => if m >= n then an else raise Universes CLASH 
	  | (Uvar(jj,(jmin,jmax,gs1,gs2)),Uconst m)
	    => (case (jmin <= m, nodLim_gt (m+1) jmax)
		  of (true,false) => (jj,(jmin,Num(m),gs1,gs2))::an
		   | (true,true)  => an
		   | (false,_)    => raise Universes LIMIT) 
	  | (Uconst n,Uvar(ii,_)) => thrd(propagate (ii,(0,n,an))) 
	  )
    | add_cnstr kk (UniGt j,an) =
      (case (fnd_nod j an,kk)
	 of (Uvar(jj,(jmin,jmax,gt,ge)),Uvar(ii,_))
	    => if member ii gt then an
	       else thrd(propagate
			 (ii,(0,(jmin+1),(jj,(jmin,jmax,ii::gt,ge))::an)))
	  | (Uconst n,Uconst m)
	    => if m > n then an else raise Universes CLASH
	  | (Uvar(jj,(jmin,jmax,gs1,gs2)),Uconst m)
	    => (case (jmin < m, nodLim_gt m jmax)
		  of (true,false) => (jj,(jmin,Num(m-1),gs1,gs2))::an
		   | (true,true)  => an
		   | (false,_)    => raise Universes LIMIT ) 
	  | (Uconst n,Uvar(ii,_)) => thrd(propagate (ii,(0,(n+1),an)))
	  ); 

  fun add_cnstrnts (kk,csts) = if !Theories.TypeType (* 2011: List.foldl *)
    		 	         then () 
			       else (UVARS:= List.foldl (add_cnstr kk) (!UVARS) csts); 

  fun ac_batch l = let
		      val uvars = !UVARS
		   in 
		      ((List.app add_cnstrnts l; true) 
		        handle Universes _ => (UVARS:= uvars; false))
		   end;

  fun uvar nam l = 
  let
    fun act() = 
      let
	val init_bod = (0,Infinity,[],[]);
	val dum_lab_bod = (Named"",init_bod)
	val lab = (NBR_UVARS:= succ(!NBR_UVARS);
		   if nam="" 
		      then Unnamed(!NBR_UVARS)
		   else Named(nam))
	val (is_old,old) = (true,ASSOC lab (!UVARS))
		            handle Assoc => (false,dum_lab_bod)
	val lab_bod =  if is_old then old else (lab,init_bod)
	val nod = Uvar(lab_bod)
      in  
	(if is_old then () else UVARS:= (lab_bod::(!UVARS));
	 add_cnstrnts(nod,l);
	 nod)
      end
  in case l
       of [UniGt(Uconst n)]                 => mkUcon(succ n) (* Uconst? *)
        | [UniGe i]                         => i
        | [UniGe(Uconst i),UniGe(Uconst j)] => mkUcon(Int.max(i,j)) (* Uconst? *)
        | _                                 => act()
  end

(* can we avoid exporting these? *) 
  fun getUniverses() = (!UVARS)
  fun setUniverses uvars = (UVARS:= uvars)

in

  fun init_universes() = (UVARS:= []; NBR_UVARS:= 0)

  fun univ_equal i j = (node_equal i j) orelse 
      		       	     (ac_batch [(i,[UniGe j]),(j,[UniGe i])]); 

  fun univ_leq i j = ac_batch [(j,[UniGe i])]

  fun univ_cmp_ b i j = if b then univ_leq i j else univ_equal i j

  fun univ_cmp i j = univ_cmp_ (!Theories.LuosMode) i j

  fun mkUvar nam = uvar nam []

  fun mkUvarGt i = uvar "" [UniGt i]

  fun mkUvarGe j i = uvar "" [UniGe(i),UniGe(j)]

(* 2011: for toc *)

  fun tocNode (Uconst n) = mkUcon (succ n)
    | tocNode    nod     = mkUvarGt nod

  fun tryUniverses f a = let
			    val uvars = !UVARS
			 in
			    ((f a) orelse (UVARS:= uvars; false))
			 end;

  fun handleUniverses f a = let
			       val uvars = !UVARS
			    in ((f a) handle e
				      => (UVARS:= uvars; raise e))	
			    end; 

  fun clean_universes() = (* 2011: List.foldl *)
    let val uvars = !UVARS
        fun cgr (nod as (n,_),new) = if mem_assoc n new then new else nod::new
    in  (UVARS:= [];   (* allow release of memory *)
         prs"clean graph: before= "; pri (length uvars);
         prs", after= "; 
         pri (length (UVARS:= List.rev (List.foldl cgr [] uvars); !UVARS));
         prnl() 
	 ) 
    end; 

end; (* local: now the graph is almost completely encapsulated! *)

end; 

(* end of Universes *)

