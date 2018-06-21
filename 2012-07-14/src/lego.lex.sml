functor LegoLexFun(structure Tokens:Lego_TOKENS
                            structure Pos:POS
                            structure Infix:INFIX
                            ):LEXER  = struct

    structure yyInput : sig

        type stream
	val mkStream : (int -> string) -> stream
	val fromStream : TextIO.StreamIO.instream -> stream
	val getc : stream -> (Char.char * stream) option
	val getpos : stream -> int
	val getlineNo : stream -> int
	val subtract : stream * stream -> string
	val eof : stream -> bool
	val lastWasNL : stream -> bool

      end = struct

        structure TIO = TextIO
        structure TSIO = TIO.StreamIO
	structure TPIO = TextPrimIO

        datatype stream = Stream of {
            strm : TSIO.instream,
	    id : int,  (* track which streams originated 
			* from the same stream *)
	    pos : int,
	    lineNo : int,
	    lastWasNL : bool
          }

	local
	  val next = ref 0
	in
	fun nextId() = !next before (next := !next + 1)
	end

	val initPos = 2 (* ml-lex bug compatibility *)

	fun mkStream inputN = let
              val strm = TSIO.mkInstream 
			   (TPIO.RD {
			        name = "lexgen",
				chunkSize = 4096,
				readVec = SOME inputN,
				readArr = NONE,
				readVecNB = NONE,
				readArrNB = NONE,
				block = NONE,
				canInput = NONE,
				avail = (fn () => NONE),
				getPos = NONE,
				setPos = NONE,
				endPos = NONE,
				verifyPos = NONE,
				close = (fn () => ()),
				ioDesc = NONE
			      }, "")
	      in 
		Stream {strm = strm, id = nextId(), pos = initPos, lineNo = 1,
			lastWasNL = true}
	      end

	fun fromStream strm = Stream {
		strm = strm, id = nextId(), pos = initPos, lineNo = 1, lastWasNL = true
	      }

	fun getc (Stream {strm, pos, id, lineNo, ...}) = (case TSIO.input1 strm
              of NONE => NONE
	       | SOME (c, strm') => 
		   SOME (c, Stream {
			        strm = strm', 
				pos = pos+1, 
				id = id,
				lineNo = lineNo + 
					 (if c = #"\n" then 1 else 0),
				lastWasNL = (c = #"\n")
			      })
	     (* end case*))

	fun getpos (Stream {pos, ...}) = pos

	fun getlineNo (Stream {lineNo, ...}) = lineNo

	fun subtract (new, old) = let
	      val Stream {strm = strm, pos = oldPos, id = oldId, ...} = old
	      val Stream {pos = newPos, id = newId, ...} = new
              val (diff, _) = if newId = oldId andalso newPos >= oldPos
			      then TSIO.inputN (strm, newPos - oldPos)
			      else raise Fail 
				"BUG: yyInput: attempted to subtract incompatible streams"
	      in 
		diff 
	      end

	fun eof s = not (isSome (getc s))

	fun lastWasNL (Stream {lastWasNL, ...}) = lastWasNL

      end

    datatype yystart_state = 
C | D | INITIAL
    structure UserDeclarations = 
      struct

(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* lego.lex *)

(* ************************ User declarations ************************ *)

structure Tokens = Tokens (* *** no longer any need to (*open Tokens*) *) 

structure Pos = Pos (* *** no longer any need to (*open Pos*) *) 

(* *** no longer any need to (*open Infix*) *) 

type ('a,'b) token = ('a,'b) Tokens.token
type pos     	   = Pos.pos
type svalue  	   = Tokens.svalue
type lexresult 	   = (svalue,pos) token

fun dummyEOF() = let val zzz = !Pos.lno
	         in  Tokens.EOF(zzz,zzz)
	         end

val eof = dummyEOF

structure KeyWord : sig
		      val find : string -> ((pos*pos)->lexresult) option
	  	    end =
  struct

	val TableSize = 401
	val HashFactor = 7

	val hash = fn s =>
	   List.foldr (fn (c,v)=>(v*HashFactor+(ord c)) mod TableSize) 0 (String.explode s)


	val HashTable = Array.array(TableSize,nil) :
		 (string * ((pos*pos)->lexresult)) list Array.array


	val add = fn (s,v) =>
	 let val i = hash s
	 in Array.update(HashTable,i,(s,v) :: (Array.sub(HashTable, i)))
	 end

        val find = fn s =>
	  let val i = hash s
	      fun f ((key,v)::r) = if s=key then SOME v else f r
	        | f nil = NONE
	  in  f (Array.sub(HashTable, i))
	  end
 
	val _ = 
	    (List.app add
        [("allE", 	    Tokens.ALLE),
         ("allI", 	    Tokens.ALLI),
         ("andE", 	    Tokens.ANDE),
         ("andI", 	    Tokens.ANDI),
	 ("AnnotateOn",     Tokens.ANNOTATEON),
	 ("AnnotateOff",    Tokens.ANNOTATEOFF),
	 ("Assumption",     Tokens.ASSUMPTION),
	 ("Double", 	    Tokens.DOUBLE),
         ("Cd", 	    Tokens.CD),
         ("Claim", 	    Tokens.CLAIM),
	 ("Configure", 	    Tokens.CONFIG),
         ("Ctxt", 	    Tokens.CTXT),
         ("Cut", 	    Tokens.CUT),
	 ("Fields", 	    Tokens.FIELDS),
         ("Inductive", 	    Tokens.INDUCTIVE),
         ("NoReductions",   Tokens.NOREDS),
         ("Parameters",     Tokens.PARAMS),
         ("Constructors",   Tokens.CONSTRS),
         ("Decls", 	    Tokens.DECLS),
         ("Discharge", 	    Tokens.DISCHARGE),
         ("DischargeKeep",  Tokens.DISCHARGEKEEP),
         ("Dnf", 	    Tokens.DNF),
	 ("Drop", 	    Tokens.EOF),
         ("echo", 	    Tokens.ECHO),
         ("Elim", 	    Tokens.ELIM),
         ("Equality", 	    Tokens.EQUALITY),
         ("Equiv", 	    Tokens.EQUIV),
         ("exI", 	    Tokens.EXI),
         ("exE", 	    Tokens.EXE),
         ("ExpAll", 	    Tokens.EXPALL),
         ("Expand", 	    Tokens.EXPAND),
         ("ExportState",    Tokens.EXPORTST),
         ("EndCase", 	    Tokens.ENDCASE),
         ("Forget", 	    Tokens.FORGET),
         ("ForgetMark",     Tokens.FORGETMARK),
         ("Freeze", 	    Tokens.FREEZE),
         ("From", 	    Tokens.FROM),
         ("Unfreeze", 	    Tokens.UNFREEZE),
         ("Gen", 	    Tokens.GEN),
         ("Generate", 	    Tokens.GENERATE),
         ("Goal", 	    Tokens.GOAL),
         ("Help", 	    Tokens.HELP),
         ("Hnf", 	    Tokens.HNF),
         ("Include", 	    Tokens.INCLUDE),
         ("Interactive",    Tokens.INTERACTIVE),
         ("Immed", 	    Tokens.IMMED),
         ("impE", 	    Tokens.IMPE),
         ("impI", 	    Tokens.IMPI),
         ("Init", 	    Tokens.INIT),
         ("Intros", 	    Tokens.INTROS),
         ("intros", 	    Tokens.iNTROS),
         ("Import", 	    Tokens.IMPORT),
         ("Induction", 	    Tokens.INDUCTION),
         ("Infix", 	    Tokens.INFIX),
         ("Inversion", 	    Tokens.INVERSION),
         ("Invert", 	    Tokens.INVERT),
         ("KillRef", 	    Tokens.KILLREF),
         ("Label", 	    Tokens.LABEL),
         ("Logic", 	    Tokens.LOGIC),
         ("left", 	    Tokens.LEFT),
         ("line", 	    Tokens.LINE),
         ("Load", 	    Tokens.LOAD),
         ("Marks", 	    Tokens.MARKS),
         ("Make", 	    Tokens.MAKE),
         ("Module", 	    Tokens.MODULE),
         ("Next", 	    Tokens.NEXT),
         ("Normal", 	    Tokens.NORMAL),
         ("NormTyp", 	    Tokens.NORMTYP),
         ("notE", 	    Tokens.NOTE),
         ("notI", 	    Tokens.NOTI),
         ("orE", 	    Tokens.ORE),
         ("orIL", 	    Tokens.ORIL),
         ("orIR", 	    Tokens.ORIR),
         ("Pbp", 	    Tokens.PBP),
         ("PbpHyp", 	    Tokens.PBPHYP),
	 ("PrettyOff", 	    Tokens.PPOFF),
	 ("PrettyOn", 	    Tokens.PPON),
	 ("PrettyWidth",    Tokens.PPLINEWIDTH),
         ("Prf", 	    Tokens.PRF),
         ("Prop", 	    Tokens.PROP),
         ("Pwd", 	    Tokens.PWD),
         ("Qnify", 	    Tokens.QNIFY),
         ("qnify", 	    Tokens.qNIFY),
	 ("Qrepl", 	    Tokens.QREPL),
         ("Refine", 	    Tokens.REFINE),
         ("Reload", 	    Tokens.RELOAD),
         ("right", 	    Tokens.RIGHT),
         ("Save", 	    Tokens.SAVE),
         ("SaveUnfrozen",   Tokens.SAVEUNFROZ),
         ("SaveFrozen",     Tokens.SAVEFROZEN),
         ("SaveObjectsOff", Tokens.SAVEOBJECTSOFF),
         ("SaveObjectsOn",  Tokens.SAVEOBJECTSON),
         ("Relation", 	    Tokens.RELATION),
         ("Theorems", 	    Tokens.THEOREMS),
         ("Theory", 	    Tokens.THRY),
	 ("StartTheory",    Tokens.STTHEORY),
	 ("EndTheory", 	    Tokens.ENDTHEORY),
         ("Record",	    Tokens.RECORD),
         ("StartTimer",     Tokens.STARTTIMER),
         ("PrintTimer",     Tokens.PRINTTIMER),
	 ("Else", 	    Tokens.TACTICELSE),
	 ("Fail", 	    Tokens.TACTICFAIL),
	 ("For", 	    Tokens.TACTICFOR),
	 ("Repeat", 	    Tokens.TACTICREPEAT),
	 ("Succeed", 	    Tokens.TACTICSUCCEED),
	 ("Then", 	    Tokens.TACTICTHEN),
	 ("Try", 	    Tokens.TACTICTRY),
         ("TReg", 	    Tokens.TREG),
         ("Type", 	    Tokens.TYPE),
         ("ElimOver", 	    Tokens.TYPESTR),
         ("TypeOf", 	    Tokens.TYPEOF),
         ("Undo", 	    Tokens.UNDO),
         ("UndoAll", 	    Tokens.UNDOALL),
         ("Unsafe", 	    Tokens.UNSAFE),
	 ("UTac", 	    Tokens.UTAC),
         ("VReg", 	    Tokens.VREG)
        ]) 
   end
(*   open KeyWord *)


local
   val commentLevel = ref 0
in
   fun initCL() = (commentLevel := 1)
   fun incCL () = (commentLevel := !commentLevel+1)
   fun decCL () = (commentLevel := !commentLevel-1)
   fun iszCL () = (!commentLevel = 0)
end

fun mkDigit (c : char) = ord c - ord(#"0")
fun mkInt (s : string) = List.foldl (fn (c,a) => a*10 + (mkDigit c)) 0 (String.explode s)

val INFIX_Ls = [Tokens.INFIX_L1,Tokens.INFIX_L2,Tokens.INFIX_L3,Tokens.INFIX_L4,Tokens.INFIX_L5,Tokens.INFIX_L6,Tokens.INFIX_L7,Tokens.INFIX_L8,Tokens.INFIX_L9]
val INFIX_Rs = [Tokens.INFIX_R1,Tokens.INFIX_R2,Tokens.INFIX_R3,Tokens.INFIX_R4,Tokens.INFIX_R5,Tokens.INFIX_R6,Tokens.INFIX_R7,Tokens.INFIX_R8,Tokens.INFIX_R9]

(* ******************* that's enough User Declarations, ed. ******************** *)

(* 2011: made dependency on structure Infix: INFIX local again *)



      end

    datatype yymatch 
      = yyNO_MATCH
      | yyMATCH of yyInput.stream * action * yymatch
    withtype action = yyInput.stream * yymatch -> UserDeclarations.lexresult

    local

    val yytable = 
Vector.fromList []
    fun mk yyins = let
        (* current start state *)
        val yyss = ref INITIAL
	fun YYBEGIN ss = (yyss := ss)
	(* current input stream *)
        val yystrm = ref yyins
	(* get one char of input *)
	val yygetc = yyInput.getc
	(* create yytext *)
	fun yymktext(strm) = yyInput.subtract (strm, !yystrm)
        open UserDeclarations
        fun lex 
(yyarg as ()) = let 
     fun continue() = let
            val yylastwasn = yyInput.lastWasNL (!yystrm)
            fun yystuck (yyNO_MATCH) = raise Fail "stuck state"
	      | yystuck (yyMATCH (strm, action, old)) = 
		  action (strm, old)
	    val yypos = yyInput.getpos (!yystrm)
	    val yygetlineNo = yyInput.getlineNo
	    fun yyactsToMatches (strm, [],	  oldMatches) = oldMatches
	      | yyactsToMatches (strm, act::acts, oldMatches) = 
		  yyMATCH (strm, act, yyactsToMatches (strm, acts, oldMatches))
	    fun yygo actTable = 
		(fn (~1, _, oldMatches) => yystuck oldMatches
		  | (curState, strm, oldMatches) => let
		      val (transitions, finals') = Vector.sub (yytable, curState)
		      val finals = map (fn i => Vector.sub (actTable, i)) finals'
		      fun tryfinal() = 
		            yystuck (yyactsToMatches (strm, finals, oldMatches))
		      fun find (c, []) = NONE
			| find (c, (c1, c2, s)::ts) = 
		            if c1 <= c andalso c <= c2 then SOME s
			    else find (c, ts)
		      in case yygetc strm
			  of SOME(c, strm') => 
			       (case find (c, transitions)
				 of NONE => tryfinal()
				  | SOME n => 
				      yygo actTable
					(n, strm', 
					 yyactsToMatches (strm, finals, oldMatches)))
			   | NONE => tryfinal()
		      end)
	    in 
let
fun yyAction0 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Pos.inc_lno(); lex()))
fun yyAction1 (strm, lastMatch : yymatch) = (yystrm := strm; (lex()))
fun yyAction2 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.SLASHS(!Pos.lno,!Pos.lno)))
fun yyAction3 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.ARROW(!Pos.lno,!Pos.lno)))
fun yyAction4 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.BACKSLASH(!Pos.lno,!Pos.lno)))
fun yyAction5 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.CHOICE(!Pos.lno,!Pos.lno)))
fun yyAction6 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.BAR(!Pos.lno,!Pos.lno)))
fun yyAction7 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.COLON(!Pos.lno,!Pos.lno)))
fun yyAction8 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.COMMA(!Pos.lno,!Pos.lno)))
fun yyAction9 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.CONTRACT(!Pos.lno,!Pos.lno)))
fun yyAction10 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.TAGBEGIN(!Pos.lno,!Pos.lno)))
fun yyAction11 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.TAGEND(!Pos.lno,!Pos.lno)))
fun yyAction12 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN C; initCL(); lex()))
fun yyAction13 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN D; lex()))
fun yyAction14 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DEQ(!Pos.lno,!Pos.lno)))
fun yyAction15 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DOT1(!Pos.lno,!Pos.lno)))
fun yyAction16 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DOT2(!Pos.lno,!Pos.lno)))
fun yyAction17 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DOT(!Pos.lno,!Pos.lno)))
fun yyAction18 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.UPARR(!Pos.lno,!Pos.lno)))
fun yyAction19 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.EQUAL(!Pos.lno,!Pos.lno)))
fun yyAction20 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.HASH(!Pos.lno,!Pos.lno)))
fun yyAction21 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LCBR(!Pos.lno,!Pos.lno)))
fun yyAction22 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LPTBR(!Pos.lno,!Pos.lno)))
fun yyAction23 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LRBR(!Pos.lno,!Pos.lno)))
fun yyAction24 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DOLLARSQ(!Pos.lno,!Pos.lno)))
fun yyAction25 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.STARSQ(!Pos.lno,!Pos.lno)))
fun yyAction26 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DOLLARSAVE(!Pos.lno,!Pos.lno)))
fun yyAction27 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DOLLARGOAL(!Pos.lno,!Pos.lno)))
fun yyAction28 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.PCTPCT(!Pos.lno,!Pos.lno)))
fun yyAction29 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LSQBR(!Pos.lno,!Pos.lno)))
fun yyAction30 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.QM(!Pos.lno,!Pos.lno)))
fun yyAction31 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RCBR(!Pos.lno,!Pos.lno)))
fun yyAction32 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RPTBR(!Pos.lno,!Pos.lno)))
fun yyAction33 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RRBR(!Pos.lno,!Pos.lno)))
fun yyAction34 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RSQBR(!Pos.lno,!Pos.lno)))
fun yyAction35 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.SEMICOLON(!Pos.lno,!Pos.lno)))
fun yyAction36 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.TILDE(!Pos.lno,!Pos.lno)))
fun yyAction37 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.UNDERSCORE(!Pos.lno,!Pos.lno)))
fun yyAction38 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.CASE(!Pos.lno,!Pos.lno)))
fun yyAction39 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.ENDCASE(!Pos.lno,!Pos.lno)))
fun yyAction40 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (
   (case Infix.infix_data yytext of 
     (Infix.LAssoc,n) => (Utils.ListUtil.nth INFIX_Ls n) (yytext,!Pos.lno,!Pos.lno)
  |  (Infix.RAssoc,n) => (Utils.ListUtil.nth INFIX_Rs n) (yytext,!Pos.lno,!Pos.lno)
  |  (_,_) 	      => Tokens.INFIX_UNREGD(yytext,!Pos.lno,!Pos.lno)))
      end
fun yyAction41 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.INT (mkInt yytext,!Pos.lno,!Pos.lno))
      end
fun yyAction42 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (Tokens.RELINT ((false,mkInt (substring (yytext,1,size(yytext)-1))),!Pos.lno,!Pos.lno))
      end
fun yyAction43 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (Tokens.RELINT ((true,mkInt (substring (yytext,1,size(yytext)-1))),!Pos.lno,!Pos.lno))
      end
fun yyAction44 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (Tokens.STRING (substring (yytext,1,size(yytext)-2),!Pos.lno,!Pos.lno))
      end
fun yyAction45 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.ID (yytext,!Pos.lno,!Pos.lno))
      end
fun yyAction46 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (case  KeyWord.find yytext
	                 of SOME tok => tok (!Pos.lno,!Pos.lno)
	                  |    	_    => Tokens.ID (yytext,!Pos.lno,!Pos.lno))
      end
fun yyAction47 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.ID (yytext,!Pos.lno,!Pos.lno))
      end
fun yyAction48 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (Pos.errmsg "Lego lexer"
	                      ("ignoring bad character "^yytext,!Pos.lno,!Pos.lno); 
                       lex())
      end
fun yyAction49 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incCL(); 
		       lex()))
fun yyAction50 (strm, lastMatch : yymatch) = (yystrm := strm;
      (decCL();
			if (iszCL()) then YYBEGIN INITIAL else ();
		       lex()))
fun yyAction51 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Pos.inc_lno(); lex()))
fun yyAction52 (strm, lastMatch : yymatch) = (yystrm := strm; (lex()))
fun yyAction53 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Pos.inc_lno(); YYBEGIN INITIAL; lex()))
fun yyQ44 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction36(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction36(strm, yyNO_MATCH)
      (* end case *))
fun yyQ43 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction31(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction31(strm, yyNO_MATCH)
      (* end case *))
fun yyQ46 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction5(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction5(strm, yyNO_MATCH)
      (* end case *))
fun yyQ45 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction40(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction40(strm, yyNO_MATCH)
      (* end case *))
fun yyQ42 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction6(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyAction6(strm, yyNO_MATCH)
            else if inp < #"."
              then if inp = #"-"
                  then yyQ45(strm', yyMATCH(strm, yyAction6, yyNO_MATCH))
                  else yyAction6(strm, yyNO_MATCH)
            else if inp = #"|"
              then yyQ46(strm', yyMATCH(strm, yyAction6, yyNO_MATCH))
              else yyAction6(strm, yyNO_MATCH)
      (* end case *))
fun yyQ41 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction21(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction21(strm, yyNO_MATCH)
      (* end case *))
fun yyQ51 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction45(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction45(strm, yyNO_MATCH)
      (* end case *))
fun yyQ57 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"-"
              then yyQ51(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ56 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ51(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ47 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction47(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ47(strm', yyMATCH(strm, yyAction47, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"("
                  then yyAction47(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"'"
                      then yyQ47(strm', yyMATCH(strm, yyAction47, yyNO_MATCH))
                      else yyAction47(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ47(strm', yyMATCH(strm, yyAction47, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction47(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ47(strm', yyMATCH(strm, yyAction47, yyNO_MATCH))
                  else yyAction47(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction47(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction47(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ47(strm', yyMATCH(strm, yyAction47, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ47(strm', yyMATCH(strm, yyAction47, yyNO_MATCH))
                  else yyAction47(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ47(strm', yyMATCH(strm, yyAction47, yyNO_MATCH))
              else yyAction47(strm, yyNO_MATCH)
      (* end case *))
fun yyQ48 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction46(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"("
                  then yyAction46(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"'"
                      then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                      else yyAction46(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction46(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                  else yyAction46(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction46(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction46(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                  else yyAction46(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
              else yyAction46(strm, yyNO_MATCH)
      (* end case *))
fun yyQ55 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #">"
              then yyQ51(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ54 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"<"
              then yyQ51(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ53 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyQ51(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ52 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction45(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\\"
              then yyQ51(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
              else yyAction45(strm, yyNO_MATCH)
      (* end case *))
fun yyQ58 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction45(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyAction45(strm, yyNO_MATCH)
            else if inp < #"["
              then if inp <= #"@"
                  then yyAction45(strm, yyNO_MATCH)
                  else yyQ58(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
            else if inp = #"a"
              then yyQ58(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
            else if inp < #"a"
              then yyAction45(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ58(strm', yyMATCH(strm, yyAction45, yyNO_MATCH))
              else yyAction45(strm, yyNO_MATCH)
      (* end case *))
fun yyQ50 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"["
              then yystuck(lastMatch)
            else if inp < #"["
              then if inp <= #"@"
                  then yystuck(lastMatch)
                  else yyQ58(strm', lastMatch)
            else if inp = #"a"
              then yyQ58(strm', lastMatch)
            else if inp < #"a"
              then yystuck(lastMatch)
            else if inp <= #"z"
              then yyQ58(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ49 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction46(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"?"
              then yyAction46(strm, yyNO_MATCH)
            else if inp < #"?"
              then if inp = #"0"
                  then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"("
                      then yyAction46(strm, yyNO_MATCH)
                    else if inp < #"("
                      then if inp = #"&"
                          then yyQ50(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                        else if inp = #"'"
                          then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                          else yyAction46(strm, yyNO_MATCH)
                    else if inp = #"*"
                      then yyQ51(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                    else if inp < #"*"
                      then yyAction46(strm, yyNO_MATCH)
                    else if inp = #"/"
                      then yyQ52(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                      else yyQ51(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp = #"<"
                  then yyQ54(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp < #"<"
                  then if inp = #":"
                      then yyQ53(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                    else if inp = #";"
                      then yyAction46(strm, yyNO_MATCH)
                      else yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp = #"="
                  then yyAction46(strm, yyNO_MATCH)
                  else yyQ55(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
            else if inp = #"_"
              then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #"["
                  then yyAction46(strm, yyNO_MATCH)
                else if inp < #"["
                  then if inp = #"@"
                      then yyQ50(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                      else yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp = #"\\"
                  then yyQ56(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                  else yyAction46(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction46(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction46(strm, yyNO_MATCH)
                  else yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
            else if inp = #"|"
              then yyQ57(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
              else yyAction46(strm, yyNO_MATCH)
      (* end case *))
fun yyQ40 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction46(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyAction46(strm, yyNO_MATCH)
            else if inp < #"["
              then if inp = #"0"
                  then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                      else yyAction46(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction46(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction46(strm, yyNO_MATCH)
                  else yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
            else if inp = #"a"
              then yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #"_"
                  then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                  else yyAction46(strm, yyNO_MATCH)
            else if inp = #"q"
              then yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
            else if inp < #"q"
              then if inp = #"p"
                  then yyQ49(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                  else yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
            else if inp <= #"z"
              then yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
              else yyAction46(strm, yyNO_MATCH)
      (* end case *))
fun yyQ39 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction37(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction37(strm, yyNO_MATCH)
      (* end case *))
fun yyQ38 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction18(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction18(strm, yyNO_MATCH)
      (* end case *))
fun yyQ37 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction34(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction34(strm, yyNO_MATCH)
      (* end case *))
fun yyQ36 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ45(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ59 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction38(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction38(strm, yyNO_MATCH)
      (* end case *))
fun yyQ35 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"!"
              then yyQ59(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ34 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction46(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"("
                  then yyAction46(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"'"
                      then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                      else yyAction46(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction46(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                  else yyAction46(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction46(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction46(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ47(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
                  else yyAction46(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ48(strm', yyMATCH(strm, yyAction46, yyNO_MATCH))
              else yyAction46(strm, yyNO_MATCH)
      (* end case *))
fun yyQ33 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction30(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction30(strm, yyNO_MATCH)
      (* end case *))
fun yyQ32 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction32(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #">"
              then yyQ45(strm', yyMATCH(strm, yyAction32, yyNO_MATCH))
              else yyAction32(strm, yyNO_MATCH)
      (* end case *))
fun yyQ61 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction9(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction9(strm, yyNO_MATCH)
      (* end case *))
fun yyQ60 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction14(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #">"
              then yyQ61(strm', yyMATCH(strm, yyAction14, yyNO_MATCH))
              else yyAction14(strm, yyNO_MATCH)
      (* end case *))
fun yyQ31 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction19(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"="
              then yyQ60(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
              else yyAction19(strm, yyNO_MATCH)
      (* end case *))
fun yyQ30 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction22(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"<"
              then yyQ45(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
              else yyAction22(strm, yyNO_MATCH)
      (* end case *))
fun yyQ29 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction35(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction35(strm, yyNO_MATCH)
      (* end case *))
fun yyQ28 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction7(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyQ45(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
              else yyAction7(strm, yyNO_MATCH)
      (* end case *))
fun yyQ62 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction41(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ62(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
            else if inp < #"0"
              then yyAction41(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ62(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
              else yyAction41(strm, yyNO_MATCH)
      (* end case *))
fun yyQ27 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction41(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ62(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
            else if inp < #"0"
              then yyAction41(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ62(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
              else yyAction41(strm, yyNO_MATCH)
      (* end case *))
fun yyQ63 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction2(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction2(strm, yyNO_MATCH)
      (* end case *))
fun yyQ26 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction40(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyAction40(strm, yyNO_MATCH)
            else if inp < #"0"
              then if inp = #"/"
                  then yyQ63(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
                  else yyAction40(strm, yyNO_MATCH)
            else if inp = #"\\"
              then yyQ45(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
              else yyAction40(strm, yyNO_MATCH)
      (* end case *))
fun yyQ65 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction16(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction16(strm, yyNO_MATCH)
      (* end case *))
fun yyQ64 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction15(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction15(strm, yyNO_MATCH)
      (* end case *))
fun yyQ25 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"2"
              then yyQ65(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"2"
              then if inp = #"1"
                  then yyQ64(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ67 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction3(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction3(strm, yyNO_MATCH)
      (* end case *))
fun yyQ66 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction43(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ66(strm', yyMATCH(strm, yyAction43, yyNO_MATCH))
            else if inp < #"0"
              then yyAction43(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ66(strm', yyMATCH(strm, yyAction43, yyNO_MATCH))
              else yyAction43(strm, yyNO_MATCH)
      (* end case *))
fun yyQ24 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction40(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyAction40(strm, yyNO_MATCH)
            else if inp < #":"
              then if inp <= #"/"
                  then yyAction40(strm, yyNO_MATCH)
                  else yyQ66(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
            else if inp = #">"
              then yyQ67(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
              else yyAction40(strm, yyNO_MATCH)
      (* end case *))
fun yyQ23 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction8(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction8(strm, yyNO_MATCH)
      (* end case *))
fun yyQ68 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction42(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ68(strm', yyMATCH(strm, yyAction42, yyNO_MATCH))
            else if inp < #"0"
              then yyAction42(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ68(strm', yyMATCH(strm, yyAction42, yyNO_MATCH))
              else yyAction42(strm, yyNO_MATCH)
      (* end case *))
fun yyQ22 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction40(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ68(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
            else if inp < #"0"
              then yyAction40(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ68(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
              else yyAction40(strm, yyNO_MATCH)
      (* end case *))
fun yyQ69 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction25(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction25(strm, yyNO_MATCH)
      (* end case *))
fun yyQ21 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction40(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyQ69(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
              else yyAction40(strm, yyNO_MATCH)
      (* end case *))
fun yyQ20 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction33(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction33(strm, yyNO_MATCH)
      (* end case *))
fun yyQ71 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction12(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction12(strm, yyNO_MATCH)
      (* end case *))
fun yyQ70 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction10(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction10(strm, yyNO_MATCH)
      (* end case *))
fun yyQ19 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction23(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\""
              then yyAction23(strm, yyNO_MATCH)
            else if inp < #"\""
              then if inp = #"!"
                  then yyQ70(strm', yyMATCH(strm, yyAction23, yyNO_MATCH))
                  else yyAction23(strm, yyNO_MATCH)
            else if inp = #"*"
              then yyQ71(strm', yyMATCH(strm, yyAction23, yyNO_MATCH))
              else yyAction23(strm, yyNO_MATCH)
      (* end case *))
fun yyQ72 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction40(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyAction40(strm, yyNO_MATCH)
            else if inp < #"["
              then if inp <= #"@"
                  then yyAction40(strm, yyNO_MATCH)
                  else yyQ72(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
            else if inp = #"a"
              then yyQ72(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
            else if inp < #"a"
              then yyAction40(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ72(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
              else yyAction40(strm, yyNO_MATCH)
      (* end case *))
fun yyQ18 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction48(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyAction48(strm, yyNO_MATCH)
            else if inp < #"["
              then if inp <= #"@"
                  then yyAction48(strm, yyNO_MATCH)
                  else yyQ72(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
            else if inp = #"a"
              then yyQ72(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
            else if inp < #"a"
              then yyAction48(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ72(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
              else yyAction48(strm, yyNO_MATCH)
      (* end case *))
fun yyQ74 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction13(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction13(strm, yyNO_MATCH)
      (* end case *))
fun yyQ73 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction28(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction28(strm, yyNO_MATCH)
      (* end case *))
fun yyQ17 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction48(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"&"
              then yyAction48(strm, yyNO_MATCH)
            else if inp < #"&"
              then if inp = #"%"
                  then yyQ73(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
                  else yyAction48(strm, yyNO_MATCH)
            else if inp = #"\\"
              then yyQ74(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
              else yyAction48(strm, yyNO_MATCH)
      (* end case *))
fun yyQ77 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction24(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction24(strm, yyNO_MATCH)
      (* end case *))
fun yyQ80 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction26(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction26(strm, yyNO_MATCH)
      (* end case *))
fun yyQ79 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"e"
              then yyQ80(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ78 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"v"
              then yyQ79(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ76 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"a"
              then yyQ78(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ83 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction27(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction27(strm, yyNO_MATCH)
      (* end case *))
fun yyQ82 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"l"
              then yyQ83(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ81 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"a"
              then yyQ82(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ75 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"o"
              then yyQ81(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ16 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction48(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"S"
              then yyQ76(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
            else if inp < #"S"
              then if inp = #"G"
                  then yyQ75(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
                  else yyAction48(strm, yyNO_MATCH)
            else if inp = #"["
              then yyQ77(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
              else yyAction48(strm, yyNO_MATCH)
      (* end case *))
fun yyQ15 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction20(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction20(strm, yyNO_MATCH)
      (* end case *))
fun yyQ85 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction44(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction44(strm, yyNO_MATCH)
      (* end case *))
fun yyQ84 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"\v"
              then yyQ84(strm', lastMatch)
            else if inp < #"\v"
              then if inp = #"\n"
                  then yystuck(lastMatch)
                  else yyQ84(strm', lastMatch)
            else if inp = #"\""
              then yyQ85(strm', lastMatch)
              else yyQ84(strm', lastMatch)
      (* end case *))
fun yyQ14 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction48(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\v"
              then yyQ84(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
            else if inp < #"\v"
              then if inp = #"\n"
                  then yyAction48(strm, yyNO_MATCH)
                  else yyQ84(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
            else if inp = #"\""
              then yyQ85(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
              else yyQ84(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
      (* end case *))
fun yyQ87 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction39(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction39(strm, yyNO_MATCH)
      (* end case *))
fun yyQ86 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction11(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction11(strm, yyNO_MATCH)
      (* end case *))
fun yyQ13 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction48(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyAction48(strm, yyNO_MATCH)
            else if inp < #"*"
              then if inp = #")"
                  then yyQ86(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
                  else yyAction48(strm, yyNO_MATCH)
            else if inp = #"]"
              then yyQ87(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
              else yyAction48(strm, yyNO_MATCH)
      (* end case *))
fun yyQ12 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction0(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction0(strm, yyNO_MATCH)
      (* end case *))
fun yyQ88 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction1(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyAction1(strm, yyNO_MATCH)
            else if inp < #"\n"
              then if inp = #"\t"
                  then yyQ88(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
                  else yyAction1(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ88(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
              else yyAction1(strm, yyNO_MATCH)
      (* end case *))
fun yyQ11 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction1(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyAction1(strm, yyNO_MATCH)
            else if inp < #"\n"
              then if inp = #"\t"
                  then yyQ88(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
                  else yyAction1(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ88(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
              else yyAction1(strm, yyNO_MATCH)
      (* end case *))
fun yyQ10 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction48(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction48(strm, yyNO_MATCH)
      (* end case *))
fun yyQ2 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyQ28(strm', lastMatch)
            else if inp < #":"
              then if inp = #"&"
                  then yyQ18(strm', lastMatch)
                else if inp < #"&"
                  then if inp = #"!"
                      then yyQ13(strm', lastMatch)
                    else if inp < #"!"
                      then if inp = #"\n"
                          then yyQ12(strm', lastMatch)
                        else if inp < #"\n"
                          then if inp = #"\t"
                              then yyQ11(strm', lastMatch)
                              else yyQ10(strm', lastMatch)
                        else if inp = #" "
                          then yyQ11(strm', lastMatch)
                          else yyQ10(strm', lastMatch)
                    else if inp = #"$"
                      then yyQ16(strm', lastMatch)
                    else if inp < #"$"
                      then if inp = #"\""
                          then yyQ14(strm', lastMatch)
                          else yyQ15(strm', lastMatch)
                      else yyQ17(strm', lastMatch)
                else if inp = #","
                  then yyQ23(strm', lastMatch)
                else if inp < #","
                  then if inp = #")"
                      then yyQ20(strm', lastMatch)
                    else if inp < #")"
                      then if inp = #"'"
                          then yyQ10(strm', lastMatch)
                          else yyQ19(strm', lastMatch)
                    else if inp = #"*"
                      then yyQ21(strm', lastMatch)
                      else yyQ22(strm', lastMatch)
                else if inp = #"/"
                  then yyQ26(strm', lastMatch)
                else if inp < #"/"
                  then if inp = #"-"
                      then yyQ24(strm', lastMatch)
                      else yyQ25(strm', lastMatch)
                  else yyQ27(strm', lastMatch)
            else if inp = #"^"
              then yyQ38(strm', lastMatch)
            else if inp < #"^"
              then if inp = #"@"
                  then yyQ18(strm', lastMatch)
                else if inp < #"@"
                  then if inp = #"="
                      then yyQ31(strm', lastMatch)
                    else if inp < #"="
                      then if inp = #";"
                          then yyQ29(strm', lastMatch)
                          else yyQ30(strm', lastMatch)
                    else if inp = #">"
                      then yyQ32(strm', lastMatch)
                      else yyQ33(strm', lastMatch)
                else if inp = #"\\"
                  then yyQ36(strm', lastMatch)
                else if inp < #"\\"
                  then if inp = #"["
                      then yyQ35(strm', lastMatch)
                      else yyQ34(strm', lastMatch)
                  else yyQ37(strm', lastMatch)
            else if inp = #"{"
              then yyQ41(strm', lastMatch)
            else if inp < #"{"
              then if inp = #"a"
                  then yyQ34(strm', lastMatch)
                else if inp < #"a"
                  then if inp = #"_"
                      then yyQ39(strm', lastMatch)
                      else yyQ10(strm', lastMatch)
                else if inp = #"o"
                  then yyQ40(strm', lastMatch)
                  else yyQ34(strm', lastMatch)
            else if inp = #"~"
              then yyQ44(strm', lastMatch)
            else if inp < #"~"
              then if inp = #"|"
                  then yyQ42(strm', lastMatch)
                  else yyQ43(strm', lastMatch)
              else yyQ10(strm', lastMatch)
      (* end case *))
fun yyQ9 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction53(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction53(strm, yyNO_MATCH)
      (* end case *))
fun yyQ1 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyQ9(strm', lastMatch)
              else yyQ1(strm', lastMatch)
      (* end case *))
fun yyQ7 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction50(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction50(strm, yyNO_MATCH)
      (* end case *))
fun yyQ6 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction52(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #")"
              then yyQ7(strm', yyMATCH(strm, yyAction52, yyNO_MATCH))
              else yyAction52(strm, yyNO_MATCH)
      (* end case *))
fun yyQ8 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction49(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction49(strm, yyNO_MATCH)
      (* end case *))
fun yyQ5 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction52(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyQ8(strm', yyMATCH(strm, yyAction52, yyNO_MATCH))
              else yyAction52(strm, yyNO_MATCH)
      (* end case *))
fun yyQ4 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction51(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction51(strm, yyNO_MATCH)
      (* end case *))
fun yyQ3 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction52(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction52(strm, yyNO_MATCH)
      (* end case *))
fun yyQ0 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"("
              then yyQ5(strm', lastMatch)
            else if inp < #"("
              then if inp = #"\n"
                  then yyQ4(strm', lastMatch)
                  else yyQ3(strm', lastMatch)
            else if inp = #"*"
              then yyQ6(strm', lastMatch)
              else yyQ3(strm', lastMatch)
      (* end case *))
in
  (case (!(yyss))
   of C => yyQ0(!(yystrm), yyNO_MATCH)
    | D => yyQ1(!(yystrm), yyNO_MATCH)
    | INITIAL => yyQ2(!(yystrm), yyNO_MATCH)
  (* end case *))
end
            end
	  in 
            continue() 	  
	    handle IO.Io{cause, ...} => raise cause
          end
        in 
          lex 
        end
    in
    fun makeLexer yyinputN = mk (yyInput.mkStream yyinputN)
    fun makeLexer' ins = mk (yyInput.mkStream ins)
    end

  end
