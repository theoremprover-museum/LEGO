(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature ANNOTATIONS =  
	  sig
		type annotation = string 
		type pathmarker = int 

		  val BEGININPUTLINE : annotation
  		  val BEGINPBP 	     : annotation
  		  val ENDPBP 	     : annotation
  		  val ENDPATH 	     : annotation
  		  val BEGINBIND      : annotation
  		  val BEGINLOUD      : annotation
  		  val ENDLOUD 	     : annotation
  		  val PATHENDMARKER  : pathmarker 
  
	  end; 


structure Annotations : ANNOTATIONS
 = 
struct

	type annotation = string 
	type pathmarker = int

(* ******* pushed here: original LEGO annotation tags ********** *)

    val BEGININPUTLINE = "\249"
    val BEGINPBP       = "\250"
    val ENDPBP 	       = "\251"
    val ENDPATH        = "\252"
    val BEGINBIND      = "\253"
    val BEGINLOUD      = "\254"
    val ENDLOUD        = "\255"

(* ******* pulled from format.sml: annotation marks ************ *

   val BEGININPUTLINE = " AAA   "(*"\249"*)
   val BEGINPBP       = " PPP   "(*"\250"*)
   val ENDPBP 	      = "   QQQ "(*"\251"*)
   val ENDPATH 	      = " III   "(*"\252"*)
   val BEGINBIND      = " ZZZ   "(*"\253"*)
   val BEGINLOUD      = " MMM   "(*"\254"*)
   val ENDLOUD 	      = "   NNN "(*"\255"*)

 * ************************************************************* *)

    val PATHENDMARKER  = 252 (* paths are int lists; this will print a \252 marker *)
   
	
end;

signature ANNOTATE = 
  sig
    val interactive : unit -> bool
    val Interactive : unit -> unit
    val interactive_push : unit -> unit
    val interactive_pop : unit -> unit
    val isAnnotating : unit -> bool
    val hasAnnotations : unit -> bool
    val SuspendAnnotations : unit -> unit
    val ResumeAnnotations : unit -> unit
    val SuspendAnnotationsDuring : ('a -> 'b) -> 'a -> 'b
    val setAnnotating : bool -> unit
    val promptAnnotating : string -> string
    val pbpAnnotate : string -> string
    val annotate_path_end : string
    val stringAnnotating : string -> string


    type path = int list
    val markup_path : path -> string
    val init_path : unit -> unit
  end;

functor FunAnnotate (structure Annotations: ANNOTATIONS)
(* *** *  
structure Annotate 
 * *** *)
	: ANNOTATE 
 = 

struct 
(* Annotations
   -----------
   are sent out by the pretty printer to efficiently communicate with
   a user-interface such as the generic Emacs interface for theorem
   provers developed by Goguen, Kleymann, Sequeira and others.
   See the LFCS Technical Report ECS-LFCS-97-368 for details.
*)

(* ************************************************************* *

   At the user level, 

     Configure AnnotateOn;

   tells the PrettyPrinter to output annotations. After

     Configure AnnotateOff;

   annotations are no longer printed. This is the default.

   Annotations should never be included in the object file.
   To temporarily suspend annotations, we use the variable
   AnnotatingNow. 

   AnnotatingNow is modified by 
   		 Interactive, 
		 SetAnnotating, 
		 SuspendAnnotations, 
		 ResumeAnnotations. 
   It is queried by isAnnotating.

   interface.sml used exit_file, go_to_file now redefined inline there

   Annotations used to be defined in Format; now they are here

 * ************************************************************ *)

 type path = int list 

local

(* interactive_mode is used to tell if in interactive mode or not.
 * it is pushed whenever a file is opened, and popped when a
 * file is closed *)

    val interactive_mode = ref ([]:bool list)
    fun interactive_push_ b = interactive_mode := b::(!interactive_mode)

    val AnnotatingNow = ref false;	(* really output annotations *)
    val Annotating = ref false;		(* in AnnotateOn mode *)

in

    fun interactive () = null(!interactive_mode);
    fun Interactive () = (interactive_mode := [];
			  AnnotatingNow:= (!Annotating))

    fun interactive_push () = interactive_push_ true
    fun interactive_pop  () = interactive_mode := tl (!interactive_mode)

    fun isAnnotating () = !Annotating andalso !AnnotatingNow
    fun hasAnnotations () = !Annotating

    fun SuspendAnnotations () = AnnotatingNow := false;
    fun ResumeAnnotations () = if interactive()
				   then AnnotatingNow := (!Annotating)
			       else ()

(* Conor sez *)
    fun SuspendAnnotationsDuring f x =
        let val _ = SuspendAnnotations ();
            val y = f x handle e => ((ResumeAnnotations ());(raise e))
            val _ = ResumeAnnotations ()
        in  y
        end

    fun setAnnotating isActive =
      (Annotating := isActive;
       AnnotatingNow := isActive)

    fun promptAnnotating s = (if isAnnotating() then (s^Annotations.BEGININPUTLINE) else s)
  
    fun pbpAnnotate s = Annotations.BEGINPBP^s^Annotations.ENDPBP
  
    val annotate_path_end = Annotations.ENDPATH

    fun stringAnnotating s = (if hasAnnotations() 
    	then (Annotations.BEGINLOUD^s^Annotations.ENDLOUD) 
	else s)

(* ************************ needs to be in Format ************************ *  
(* This is a hack from legoformat.sml: pbpAnnotate adds 250 and 251 codes. *)

    fun path_wrap l bls = 
	  if isAnnotating () then 
	      (annotate (List.rev l))::(bls@[annotate [PATHENDMARKER]]) (* *** below: str252 *** *)
	  else bls 

 * ************************ needs to be inFormat ************************* *)  

    local (* all of these have been lifted out now *)
		
	val last_path = ref ([]: int list)

    (* ******** str252 is for path_wrap triggering PBP markup: \250 and \251 **** *)
    (* ******** str252 s = s <> [] andalso (hd s) = 252 ************************* *)

	    fun str252   []   = false
    	      | str252 (h::t) = h = Annotations.PATHENDMARKER;

    (* *** a path is a Proof-by-pointing structure for indexing extents ***** *)
	fun compress_path t =

	    	let fun slice i old [] = [i]
		      | slice i [] new = i::new
		      | slice i (p::old) (n::new) = 
		      	if p = n then slice (i+1) old new else i::n::new
	    	in 

    (* ***** fn x => chr (x+128) is for Proof-by-pointing under PG/PBP ***** *)
		    let val path' = slice 0 (!last_path) t
		    in (last_path := t; 
		        String.implode (List.map (fn x => Char.chr (x+128)) path'))
		    end
	    	end
	    
	 fun annotate_path t = pbpAnnotate (compress_path t)

	in

	    fun markup_path s = if (str252 s) 
				    then annotate_path_end 
			          else 
				    annotate_path s

	    fun init_path () = (last_path:=[])
	
	end; 

(* ******* pulled from format.sml: annotation tags ************ *)


(* this now needs to move to format.sml because we don't have message defined yet *)

(* **** *
    fun SetAnnotating isActive =
      (setAnnotating isActive;
       message ("Annotating is now "^
		(if isActive then "enabled" else "disabled")))

 * **** *)

end;


end;

structure Annotate = FunAnnotate(structure Annotations=Annotations);


