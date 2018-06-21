(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* $Id: modules.sml,v 1.12 1998/11/10 15:29:13 ctm Exp $ *)

functor FunModules(
	structure Term:TERM 
	structure Context:CONTEXT 
	structure Top:TOP 
	structure Toplevel:TOPLEVEL 
	structure Namespace:NAMESPACE 
	structure Pretty:PRETTY 
	sharing 
		type Term.cnstr 
		   = Context.cnstr 
		   = Namespace.cnstr 
		   = Pretty.cnstr  
	and 
		type Term.binding  
		   = Context.binding  
		   = Namespace.binding  
		   = Pretty.binding  
	and 
		type Context.context  
		   = Namespace.context  
		   = Pretty.context  
	) 

(* *** * 
structure Modules
 * *** *)
	: MODULES 
	  
 = 

struct

(* filename utilities *)

datatype inputKind = SRC | OBJ | NAM | INTERACTIVE 

local 

      val bug = Utils.Except.bug
      val failwith = Utils.Except.failwith 

      val earlier = Utils.Timing.earlier  

in 

val lp_ext = 
  fn SRC => (fn nam => nam^".l")
   | OBJ => (fn nam => nam^".o")
   | NAM => (fn nam => nam)
   |  _  => bug"no file name extension for interactive input"
	
		
local
	val split_ext =
	  fn (#"l")::(#".")::crest => (crest, SRC)
	   | (#"o")::(#".")::crest => (crest, OBJ)
	   |                 cfnam => (cfnam, NAM)

    	fun to_frst_slash so_far =
	      fn      []              => (so_far,[])
 	      | (rest as ((#"/")::t)) => (so_far,rest)
 	      |      h::t             => 
			let 
			  val (nam,rest) = (to_frst_slash so_far t)
			in (h::nam,rest)
			end
in
	fun splitPath path =
	  let
	    val (crest,ext) = split_ext (List.rev (String.explode path))
	    val (cnam,cpath) = to_frst_slash [] crest
	  in
	    (String.implode (List.rev cpath),String.implode (List.rev cnam),ext)
	  end
end;

(* searching for files *)
local

  fun find_file name = 
    let
      fun ff snam =   (* for following symbolic links *)
(* ******************************************************* *
	given the changes to OS.Path and OS.FileSys
	this code may need a serious overhaul
	and hopefully with it, some simplification!!!
 * ******************************************************* *)
	let 
	    val rpath = OS.FileSys.realPath snam
	    val dflag = OS.FileSys.isDir   rpath
	    val sflag = OS.FileSys.isLink  rpath
	 in
	    if 
		dflag then NONE
	    else
		if sflag
		  then 
		    let 
			val rlink = OS.FileSys.readLink snam
			val aflag = OS.Path.isAbsolute rlink
			val {dir=rldir,...} = OS.Path.splitDirFile rlink
		    in
			ff (if aflag then rlink 
			    else OS.Path.concat(rldir, rlink))
		    end
		else 
		let 
		    val mtime = OS.FileSys.modTime rpath
		    val rflag = OS.FileSys.access (snam,[OS.FileSys.A_READ])
		in  
		   SOME (name, mtime, rflag)
		end

	end handle OS.SysErr _ => NONE
	    handle OS.Path.Path => NONE
    in ff name
    end
  
  fun slash_or_tilde_cp c = (ord c = ord #"/") orelse (ord c = ord #"~")

  fun slash_or_tilde_sp name = case (String.explode name) of
                                 (c::[]) => slash_or_tilde_cp c
				|   _    => false

  fun find_file_using_legopath ext fname =
    let
      val name = lp_ext ext fname
      fun ffp [] = NONE
	| ffp (h::t) = (case find_file (h^name)
			  of NONE => ffp t
			   | x => x)
    in
      if (slash_or_tilde_sp name)
	then find_file name
      else ffp (Top.legopath())
    end

  fun check_file_ok nam =
    fn SOME(filnam,tim,true) => (filnam,tim)
     | SOME(filnam,_,false) =>
	 failwith("Searching for file "
		  ^nam^";\nfound "
		  ^filnam^",\nbut you can't read it.")
     | NONE =>
	 failwith("Searching for file "
		  ^nam^";\nno appropriate file found.")

in

  fun find_file_dotl      nam =
    case splitPath nam
      of (_,_,NAM) => check_file_ok nam (find_file_using_legopath SRC nam)
       | (_,_,SRC) => check_file_ok nam (find_file_using_legopath NAM nam)
       | (_,_,OBJ) => check_file_ok nam (find_file_using_legopath NAM nam)
       | _ => bug"find_file_dotl"

  fun find_file_dotl_doto nam =
    case splitPath nam
      of (_,_,SRC) => check_file_ok nam (find_file_using_legopath NAM nam)
       | (_,_,OBJ) => check_file_ok nam (find_file_using_legopath NAM nam)
       | (_,_,NAM) => 
	     let
	       val doto = find_file_using_legopath OBJ nam 
	       val dotl = find_file_using_legopath SRC nam 
	       val newer =
		 case (doto,dotl)
		   of (NONE,SOME(_)) => dotl
		    | (SOME(_),NONE) => doto
		    | (SOME(_,otim,_),SOME(_,ltim,_)) =>
			if earlier (otim,ltim) then dotl
			else doto
		    | _ => NONE
	     in check_file_ok nam newer
	     end
       | _ => bug"find_file_dotl_doto"
end

end;

local 

      val bug      = Utils.Except.bug
      val failwith = Utils.Except.failwith 

      val dquote     	= Utils.StringUtil.dquote
      val concat_space  = Utils.StringUtil.concat_space

      val member  = Utils.ListUtil.member 

      val earlier = Utils.Timing.earlier  
      val makestring_timer = Utils.Timing.makestring_timer  

      val message     = Printing.message  
      val loudmessage = Printing.loudmessage  

      val prts     = Printing.prts 
      val prtnl    = Printing.prtnl 
      val prtsp    = Printing.prtsp 
      
      val os_prnt_exp = Pretty.os_prnt_exp  
      val os_prnt_red = Pretty.os_prnt_red  

      	  open Term 

      val unCxt = Context.unCxt
      val splitCxt = Context.splitCxt

in 

(* ******************************************************* *
(* output "compiled" state: ".o" files *)
 * ******************************************************* *)

fun writeCompiled filenam modnam =
  let
    val (hit,new,old) = splitCxt (sameMrk modnam) (* splitCxt in Context *)
      ("Mark "^dquote(modnam)^" not found; "^lp_ext OBJ modnam^" not written")
      (Namespace.getNamespace())

    val new = unCxt new (* hit::new *)

    fun compile os br =
      let

	val prs     = prts os 
  	fun prnl()  = prtnl os
  	fun prsp()  = prtsp os

	fun pr_sc   () = prs ";" 
	fun pr_nl   () = prs "\n" 
	fun pr_scnl () = (pr_sc();pr_nl())

	val prnt_exp = os_prnt_exp os 
	val prnt_red = os_prnt_red os 

	fun pr_deps br =
	  let val deps = ref_deps br
	  in  if (null deps) then ()
	      else prs ("//"^(concat_space deps))
	  end

  	fun lgDefn br =
	  let val (v,t) = ref_vt br
	  in  prs ((if (ref_isFrozen br) then"*"
			else if (ref_isLocal br)  then "$" else "")^
		       "["^ref_nam br^" : ");
	      prnt_exp t;
	      prs "\n  = "; 
	      prnt_exp v;
	      pr_deps br; prs "]";
	      pr_scnl()
	  end

	fun lgDecl br =
	  (prs ((if (ref_isGlobal br) then "$" else "")^"["^ref_nam br^
		    " "^prHidSym(ref_vis br)^" ");
	   prnt_exp (ref_typ br); pr_deps br; prs "]";
	   pr_scnl())

  	fun lgRed br = 
	  (prnt_red (ref_red br); 
	   pr_scnl())

  	fun lgConfig (cfg as (a,(x,y,z))) = 
	  (prs ("Configure "^a^" "^x^" "^y^" "^z); 
	   pr_scnl())

	fun lgMark (mrk as (s,i,_,_)) = 
	  (prs ("Module "^s^
	  	     (if (null i) then ""
		      else " Import "^concat_space(List.map dquote i))); 
	   pr_scnl())

        local
            fun t2s2 b [] = "!)"
              | t2s2 b (h::t) = (if b then "(!" else " ")^h^(t2s2 false t)
	in  
            fun tag2string [] = "(! !)"
              | tag2string x = t2s2 true x

	    fun lgTag tag = prs ("Generate "^(tag2string tag)^" ")

	    fun lgLab (tag,name) = prs ("Label "^(tag2string tag)^" "^name^";") 

        end

      in
	if Namespace.activeProofState()
	  then failwith("Hit eof of module "^dquote(modnam)
			^"\n  while still in proof state; "
			^dquote(filenam)^" not written")
	else
	  case (ref_kind br,ref_isDefn br)
	    of (Bnd,true)        => lgDefn br
	     | (Bnd,false)       => lgDecl br
             | (GenTag tag,true) => lgTag tag 
             | (GenTag _,false)  => failwith("Cannot write Generated declaration")
	     | (Red,_)           => lgRed br 
	     | (Mrk mrk,_)       => lgMark mrk
	     | (Config cfg,_)    => lgConfig cfg
             | (LabelTag lab,_)  => lgLab lab
	     | (StThry nam,_)    => failwith("Cannot write OBJ files while Theory "
					      ^dquote(nam)^" is unclosed")
      end

    fun writeIt (filenam, new) = let (* throws IO.Io, so finalisation may fail *)
    			       	     val os = TextIO.openOut filenam
    				     val _ = List.map (compile os) new 
    				     val _ = TextIO.closeOut os
				 in
				     message ("Wrote "^filenam)
				 end
  in

    Annotate.SuspendAnnotationsDuring writeIt (filenam, hit :: new)

  end handle IO.Io s => message("Warning: "^(#name s)^"\n"^filenam^" not written");

(* ******************************************************* *
(* * commands to support Luca's 'mock modules' * *)
 * ******************************************************* *)

datatype LoadKind = LK_INTERACTIVE
  		  | LK_STRING 
  	 	  | LK_MAKE of string
  		  | LK_MAKEUNSAFE of string
  		  | LK_LOAD of string
  		  | LK_INCLUDE of string
  		  | LK_DEPCHECK of string list

datatype stamp = Stamp of (string*Time.time) * LoadKind * bool

(* in modules.sig; not implemented until 2011-10-07 !!! *)

fun isDepChecking (Stamp (_,_,b)) = b 

fun getFileName (Stamp ((filnam,_),_,_)) = filnam 

(* *)

fun when () = Time.now () (* Time.zeroTime??? *)

fun initStampString      () = Stamp (("",when()), LK_STRING,      false)
fun initStampInteractive () = Stamp (("",when()), LK_INTERACTIVE, false)

(* "forward referencing" so the actions of the grammar can
 * parse files (e.g. 'Include') and strings (e.g. 'Logic')
 *)

val legoFileParser = ref (fn (stmp:stamp) =>
			   fn (clos:unit->unit) => ())

val legoStringParser = ref (fn (str_nam:string) => ());

(* Switch for saving objects back, or not *)

val objectSave = ref true;

fun SetSaveObjects x = objectSave:=x;

fun findMrk mrk = List.find (sameMrk mrk) (Namespace.getBindings()) 

fun foundMrk mrk = case (findMrk mrk) of SOME(_) => true | NONE => false

(* the time field of mit is the time the file was opened;  *
 * Namespace.addMark also stores the time the mark is made *)

fun Mark (mrk,imports,name,time) =
  if 
	Namespace.activeProofState() 
  then 
	failwith"no marking in proof state"
  else if (foundMrk mrk)
	 then failwith("Mark "^dquote(mrk)^" already in namespace")
       else 
	  (loudmessage("Creating mark "^dquote(mrk)^" ["^name^"]");
		 Namespace.addMark (mrk,imports,time)
	   ); 

(* Exception for aborting parser after modules declaration *)

exception DepCheckDone of string list;

local
  fun includ stmp clos = (Namespace.KillRef(); (!legoFileParser) stmp clos)

  fun mk_ld filnam ff lk =
    let
      val (_,nam,_) = splitPath filnam
    in
      if foundMrk nam
	then message("Module "^dquote(nam)^" already loaded: no action")
      else let
	     val (nt as (fullpath,_)) = ff filnam
	     val (path,_,ext) = splitPath fullpath
	     fun closing() =
                 (let 
		    val mark = findMrk nam
	          in (case mark
	            of SOME(br) => message("(** time since mark "^dquote(nam)
		 	  		   ^": "^makestring_timer (ref_marktim br)
					   ^" **)")
  		     | NONE => message("Warning: expected mark "^dquote(nam) 
			 		^" not found");
		      if ext=SRC then (writeCompiled (path^lp_ext OBJ nam) nam)
		      else ())
		  end)
	      val mk_ld_stmp = Stamp(nt,lk nam,false)
	      val mk_ld_clos = if !objectSave 
				  then closing 
                   	       else (fn() => 
			message ("Object file "^(lp_ext OBJ nam)^" file not written.")
					 )
	   in 
		includ mk_ld_stmp mk_ld_clos
	   end
    end

in

  fun ForgetOld fnam =
    let 
	val (_,oldnam,_) = splitPath fnam
    in  
	case (findMrk oldnam) of 
	         NONE   => ()
	     | SOME(br) => 
		   let 
			val (_,modtime) = find_file_dotl fnam 
		   in  
			if earlier(ref_filtim br,modtime) 
			   then Namespace.ForgetMrk oldnam
			else ()
		   end
      end

  fun Include nam = 
    let
	val stmp = Stamp(find_file_dotl nam,LK_INCLUDE nam,false)

	fun clos () = ()
    in
	includ stmp clos
    end

  fun MakeFalse  filnam = 
	mk_ld filnam find_file_dotl_doto LK_MAKE

  fun Make_ initial filnam = (
    if 
	initial 
    then 
       (message ("Checking Dependencies for "^filnam); 
        ForgetOld filnam;  (* Just in case file not on lego path *)
	let
	    val stmp = Stamp (find_file_dotl filnam, LK_DEPCHECK [filnam], true)
	    fun clos () = ()
	in
	    includ stmp clos
	end
            handle DepCheckDone _ =>  message ("Dependencies Checked")
	)
     else ();  
	MakeFalse  filnam)

  fun Make filnam = Make_ true filnam

  fun MakeUnsafe filnam = 
	mk_ld filnam find_file_dotl_doto LK_MAKEUNSAFE

  fun Load filnam = 
	mk_ld filnam find_file_dotl LK_LOAD

  fun ReloadFrom loadFilnam forgetFilnam =
    let
      val (_,forgetNam,_) = splitPath forgetFilnam
    in
      (if foundMrk forgetNam 
	then Namespace.ForgetMrk forgetNam 
	else ();
       Load loadFilnam)
    end

  fun DepCheck (Stamp(_,LK_DEPCHECK(done_list),true)) (nam,imports) =
    
    let 
	fun loop done [] = raise (DepCheckDone done)
	  | loop done (module::rest) = 
	      if member module done 
		  then loop done rest
	      else 
		(let
		     val stmp = Stamp(find_file_dotl module,LK_DEPCHECK done, true)
		     fun clos () = ()
		 in
		     includ stmp clos
		 end
		 handle DepCheckDone(newdone) => loop newdone rest
                )
    in 
	loop (nam::done_list) imports
    end
    | DepCheck _ _ = bug "DepCheck: Unexpected Arguments"

  fun ModuleImport (Stamp((filenam,filetim),ldknd,xec)) (nam,imports) =

    let
      val (_,Nam,_) = splitPath filenam
      val _ = if foundMrk nam
		then failwith("Trying to Include module "^dquote(nam)^
			 " which already exists.  Use Make, Load or Reload")
	      else message ("Including module "^nam)
      val _ = if (nam<>Nam) andalso (not (Annotate.interactive()))
		then message("Warning: module name "^dquote(nam)
			     ^" does not equal filename "^dquote(filenam)^"!")
	      else ()
    in
      ((case ldknd
	 of LK_INCLUDE lnam 	=>
		      (message("Warning: Including file "
			       ^lnam^" which contains Module "
			       ^nam^"; Imports propagated as Include");
		       		   (List.app Include imports))
	  | LK_LOAD _ 		=> (List.app Load    imports)
	  | LK_MAKE _ 		=> (List.app MakeFalse imports)
          | LK_DEPCHECK _ 	=> bug "ModuleImport: DepCheck"
	  | LK_INTERACTIVE	=> (List.app MakeFalse imports)
	  | LK_STRING =>
		       (message("Warning: Use of Module command in string.");
				   (List.app MakeFalse imports))

	  | _ 			=> bug"ModuleImport") 
	; 
         Mark (nam,imports,filenam,filetim)
	)
    end

    fun ModuleHeader filnamstmp nam_imports = 
        if (isDepChecking filnamstmp) 
	   then DepCheck filnamstmp nam_imports 
	else ModuleImport filnamstmp nam_imports 

end (* of local defn of  includ, mk_ld *)

end (* of topmost local *)
end; (* struct *)

