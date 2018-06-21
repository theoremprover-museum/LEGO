(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* modified 

   09 nov 2009 printing lifted from here to format.sml 

*)

(* modified 22 nov 2009 *)

(* legoutils.sml *)

structure Utils  : UTILS = 
struct

(* ******************************************************** *
(* New Jersey special, for use in toplevel *)
 * ******************************************************** *)

(* Pointer equality !!! *)
fun UNSAFEeq(x:'a,y:'a) = 
      (Unsafe.cast(x): 'a ref) = (Unsafe.cast(y): 'a ref); 


(* ********************************************************
	top-level exceptions	
 * ******************************************************** *)

structure Except = 
struct
(* failure, bug, and warning *)
exception Failure of string (* available as Fail at SML toplevel *)
  fun failwith s = raise Failure s

exception Bug of string
  fun bug s = raise Bug ("\nbug detected at "^s)

(* try raise finally: do beg(), then f x then end(), even if f raise exn e *)

fun try_raise_finally initialise f finalise x =
        let val y = initialise x
            val z = (f y) handle e => ((finalise y);(raise e))
            val _ = finalise y
        in  z
        end
end;

(* ********************************************************
   should be kitted with some top-level monadic bindings
   ******************************************************** *)

structure Modif = 
struct  
(* 2011: one or two "Umod"s crept in? *) 

(* structure sharing *)
datatype 'a modif = Mod of 'a | UMod;

fun share f x =
  case (f x) of (Mod y) => y | UMod => x;

fun share2 (f1,f2) (xy as (x,y)) =
  case (f1 x,f2 y)
    of (Mod x', Mod y') => Mod(x',y')
     | (Mod x',  UMod ) => Mod(x',y )
     | ( UMod,  Mod y') => Mod(x, y')
     | ( UMod,   UMod ) => UMod

fun share2f f xy = share2 (f,f) xy

fun map_share f =  
    let 
	fun map_share_f (x::l) =
            (case (f x)
	       of (Mod x') => Mod(x'::share_map_share_f l)
	        |   UMod   => (case map_share_f l
			         of (Mod l') => Mod (x::l')
			          |   UMod   => UMod))
	  | map_share_f   []   = UMod
        and share_map_share_f l = share map_share_f l
    in 
	map_share_f 
    end;

fun post_share f a g c = 
    case f a 
      of UMod  => c
       | Mod b => g b 

end;

(* ******************************************************** *
	surely not??? surely all these could be removed
 * ******************************************************** *)
structure Counting = 
struct 

fun succ n = n + 1
fun pred n = n - 1

fun counter (n:int) = (* for timestamp() *)
    let
	val counter = ref n
    in 
        fn () => (counter:=succ(!counter);!counter)
    end

fun Counter n = (* for manageVars() *)
    let 
    	val counter = ref n
	fun init() = (counter:=n)
	fun tick() = (counter:=succ(!counter))
	fun read() = (!counter)
    in  
    	(init, tick, read)
    end 

end;



(* ******************************************************** *)
structure ListUtil = 
struct 

(* ******************************************************** * 
(* 	should be removed: more list primitives		    *)

(* List.app plus General.ignore *)
fun do_list f [] = ()
  | do_list f (h::t) = (f h; do_list f t)

(* list operators *)
fun foldr f a (x::xs) = f x (foldr f a xs)
  | foldr f a []      = a
fun foldl f a (x::xs) = foldl f (f a x) xs
  | foldl f a []      = a

exception Empty of string

fun last []  = raise Empty "last"
  | last [x] = x
  | last (x::xs) = last xs

fun dropLast []  = raise Empty "dropLast"
  | dropLast [x] = []
  | dropLast (x::xs) = x :: dropLast xs

fun removeLast l = (last l, dropLast l)
      handle Empty _ => raise Empty "removeLast"
	
fun foldr1 f [] = raise Empty "foldr1"
  | foldr1 f l  = let val (last,front) = removeLast l
		  in  foldr f last front
		  end
 * ******************************************************** *)

(* do not change order of list *)
(* ******** *
   List.partition f l
    applies f to each element x of l, from left to right, 
    and returns a pair (pos, neg) where 
    pos is the list of those x for which f x evaluated to true, 
    and neg is the list of those for which f x evaluated to false. 
    The elements of pos and neg retain the same relative order they possessed in l.

fun filter_split p l = (List.partition p l)
(*    let fun select x (res_pos,res_neg) =
      if p x then (x::res_pos,res_neg) else (res_pos,x::res_neg)
    in foldr select ([],[]) end *)

 * ******** *)

fun filter_pos p l = #1 (List.partition p l)
(*    let fun select x res = if p x then x::res else res
    in foldr select [] l end *)

fun filter_neg p l = #2 (List.partition p l)
(*    let fun select x res = if p x then res else x::res
    in foldr select [] l end *)


(* List.nth *)
(* ******** *
   List.nth (l, i)
    returns the i(th) element of the list l, counting from 0. 
    It raises Subscript if i < 0 or i >= length l. 
    We have nth(l,0) = hd l, ignoring exceptions.
 * ******** *)
exception Nth of int
fun nth l n = List.nth (l,n-1) handle Subscript => raise Nth n 

fun first_n n l = List.take(l,n) handle Subscript => Except.failwith "first_n"

(* List.find *)
(* ********* *
   find f l
    applies f to each element x of the list l, 
    from left to right, until f x evaluates to true. 
    It returns SOME(x) if such an x exists; otherwise it returns NONE.

   find f   []   = NONE
   find f (h::t) = if (f h) then SOME h else find f t
 * ********* *)

fun member x xs   = List.exists (fn z => z=x) xs

fun add_if_missing i l = if (member i l) then l else i::l

fun diff []     _ = []
  | diff (h::t) s = if (member h s) then diff t s
	 	    else h::(diff t s)

(* Association lists *)
(* mem_assoc is the domain predicate for assoc *)
fun equal_fst u (x,_) = (u=x) 

fun mem_assoc u l = List.exists (equal_fst u) l
exception Assoc
fun ASSOC e l = valOf (List.find (equal_fst e) l) handle Option => raise Assoc 
fun assoc e l = #2 (ASSOC e l) (* used in lots of places *)

fun prune e l = filter_neg (equal_fst e) l (* prune an assoc list *)

end;

structure StringUtil = 
struct 
(* string operators *)
val   nullString = String.implode []
val isNullString = fn "" => true | _ => false
val spaceChar =  #" "
val spaceString = String.str spaceChar
val WILDCARD  = "_"
val HYPNAME   = "H"
val ZZZNAME   = "z"

fun wildcard_ b s = if b then WILDCARD else s
fun wildcard s = wildcard_ (isNullString s) s

val isWILDCARD = fn "_" => true | _ => false

fun spaces n = let 
    	       	   fun spaces_ n cs = if (n <= 0) then cs 
		       	       	        else spaces_ (n-1) (spaceChar::cs)
	       in 
		  String.implode (spaces_ n [])
	       end 
local 

  fun bb l r m = l^m^r
  val SQUOTE = "'"
  val DQUOTE = "\""

in

  val square = bb "[" "]"
  val parens = bb "(" ")"
  val curly = bb "{" "}"
  val pointed = bb "<" ">"

  val legocomment = bb "(* " " *)"

  val squote = bb SQUOTE SQUOTE
  val dquote = bb DQUOTE DQUOTE

end

(* lists of strings *)
(* ********************* *
   String.concatWith s l
    returns the concatenation of the strings 
    in the list l using the string s as a separator. 
    This raises Size if the size of the resulting string 
    would be greater than maxSize.

 * ********************* *)

fun concat_sep sep l = String.concatWith sep l

val concat_space = concat_sep spaceString
val concat_comma = concat_sep "," 


(* *** two functional fresh name generators for gensym() *** *)
(* *** okLoc checks nam locally 
 * *** okGlb carries other parameters from outer scopes (e.g. contexts) to check nam
 * *** then it's the usual state-monad with state = nams for fresh_push
 * ***)

fun fresh okLoc okGlb nam nams =
let 
    fun fresh_ n = 
    	if (okLoc n) orelse (not (ListUtil.member n nams) andalso (okGlb n))
   	   then n
	else let 
	     	 val new = (n^"'"^(Int.toString (Counting.succ(length nams))))
	     in  
	     	 (fresh_ new)
	     end
in	(* I always hated the prime"'" but everything else is illegal or ambiguous! *)
    fresh_ nam
end

(* *** lemma fresh_push nam nams = (n, n::nams), where n = fresh nam nams *** *)

fun fresh_push okLoc okGlb nam nams =
let 
    val n = fresh okLoc okGlb nam nams
in	
    (n, n::nams)
end

end;


(* ********************************************************
	all now handled better and more uniformly by Timer
   ******************************************************** *)

structure Timing = 
struct 
(* Timers *)
local
  open Time
  open Timer
in
  type timer = cpu_timer
  type time = time
  val start_timer = startCPUTimer
  val check_timer = checkCPUTimer

  fun mks_time (t:time) = 
	let
	    val NANO = 1000000000.0
	    fun fromNanoseconds t = t/NANO
	    val muI  = toNanoseconds t
	    val muR  = Real.fromLargeInt muI
	    val secs = fromNanoseconds muR
	in 
	   " "^Real.toString secs^"s; "

	end

  fun sub_time (t1:time, t2:time) = t1 - t2
  fun earlier (t1:time, t2:time)  = t1 <= t2

  fun makestring_timer t =
    let
      val non_gc_time = #usr (check_timer t)
      val gc_time = checkGCTime t
      val sys_time = #sys (check_timer t)
    in
      "time="^(mks_time non_gc_time)^
      "  gc="^(mks_time gc_time)^
      "  sys="^(mks_time sys_time)
    end

  fun print_timer t = (StringUtil.spaces 3)^StringUtil.legocomment(makestring_timer t)

  fun timer_wrapper f x = 
      let 
      	  val t = start_timer ()
	  val y = f x
	  val s = print_timer t
      in
	  (y,s)
      end

end

end;


(* ******************************************************** *)

structure FunUtil =  
struct 
(* functional iteration utilities *)
fun repeat n action arg = (* used 1x in tacticals.sml *)
    let fun repeat_action n =
            if n <= 0 then () else (action arg; repeat_action (n-1))
     in repeat_action n end

fun Repeat n fnc arg = if (n<=0) then arg (* used 1x in synt.sml *)
                       else fnc (Repeat (n-1) fnc arg);

(* wrong CBV!: expects fnc to eventually raise an exception *)
(* fun Forever  fnc arg = fnc (Forever fnc arg); *)
exception UntilExn
fun Until fnc arg = ((Until fnc (fnc arg)) handle UntilExn => arg)

(* apply to a pair *)
fun diag_fun f = (f,f);
fun pair_fun_apply (f,g) (x,y) = (f x,g y);
fun pair_apply f (x,y) = (f x, f y) (* pair_fun_apply (diag_fun f) (x,y); *)

end; 

(* ******************************************************** *)

(* a tail recursion *)
fun interval n m =
    let fun interval_n (l,m) =
            if n > m then l else interval_n (m::l, m-1)
     in interval_n ([],m) end; 


end; (*struct *)

(* last modified 15 nov 2011 *)
