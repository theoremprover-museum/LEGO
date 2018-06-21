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

%%
%s C D;
%header (functor LegoLexFun(structure Tokens:Lego_TOKENS
                            structure Pos:POS
                            structure Infix:INFIX
                            ):LEXER);

alpha = [A-Za-z];
digit = [0-9];
ws = [\ \t];
infsym = [+-/*]|"<<"|">>"|"/\\"|"\\/"|"|-"|"::"|&[a-zA-Z]+|@[a-zA-Z]+;
commentopen = "(*";
commentclos = "*)";

%%
<INITIAL>\n        => (Pos.inc_lno(); lex());
<INITIAL>{ws}+     => (lex());
<INITIAL>"//"      => (Tokens.SLASHS(!Pos.lno,!Pos.lno));
<INITIAL>"->"      => (Tokens.ARROW(!Pos.lno,!Pos.lno));
<INITIAL>"\\"      => (Tokens.BACKSLASH(!Pos.lno,!Pos.lno));
<INITIAL>"||"      => (Tokens.CHOICE(!Pos.lno,!Pos.lno));
<INITIAL>"|"       => (Tokens.BAR(!Pos.lno,!Pos.lno));
<INITIAL>":"       => (Tokens.COLON(!Pos.lno,!Pos.lno));
<INITIAL>","       => (Tokens.COMMA(!Pos.lno,!Pos.lno));
<INITIAL>"==>"     => (Tokens.CONTRACT(!Pos.lno,!Pos.lno));
<INITIAL>"(!"      => (Tokens.TAGBEGIN(!Pos.lno,!Pos.lno));
<INITIAL>"!)"      => (Tokens.TAGEND(!Pos.lno,!Pos.lno));
<INITIAL>{commentopen}      => (YYBEGIN C; initCL(); lex());
<INITIAL>"%\\"     => (YYBEGIN D; lex());
<INITIAL>"=="      => (Tokens.DEQ(!Pos.lno,!Pos.lno));
<INITIAL>".1"      => (Tokens.DOT1(!Pos.lno,!Pos.lno));
<INITIAL>".2"      => (Tokens.DOT2(!Pos.lno,!Pos.lno));
<INITIAL>"."       => (Tokens.DOT(!Pos.lno,!Pos.lno));
<INITIAL>"^"       => (Tokens.UPARR(!Pos.lno,!Pos.lno));
<INITIAL>"="       => (Tokens.EQUAL(!Pos.lno,!Pos.lno));
<INITIAL>"#"       => (Tokens.HASH(!Pos.lno,!Pos.lno));
<INITIAL>"{"       => (Tokens.LCBR(!Pos.lno,!Pos.lno));
<INITIAL>"<"       => (Tokens.LPTBR(!Pos.lno,!Pos.lno));
<INITIAL>"("       => (Tokens.LRBR(!Pos.lno,!Pos.lno));
<INITIAL>"$["      => (Tokens.DOLLARSQ(!Pos.lno,!Pos.lno));
<INITIAL>"*["      => (Tokens.STARSQ(!Pos.lno,!Pos.lno));
<INITIAL>"$Save"   => (Tokens.DOLLARSAVE(!Pos.lno,!Pos.lno));
<INITIAL>"$Goal"   => (Tokens.DOLLARGOAL(!Pos.lno,!Pos.lno));
<INITIAL>"%%"      => (Tokens.PCTPCT(!Pos.lno,!Pos.lno));
<INITIAL>"["       => (Tokens.LSQBR(!Pos.lno,!Pos.lno));
<INITIAL>"?"       => (Tokens.QM(!Pos.lno,!Pos.lno));
<INITIAL>"}"       => (Tokens.RCBR(!Pos.lno,!Pos.lno));
<INITIAL>">"       => (Tokens.RPTBR(!Pos.lno,!Pos.lno));
<INITIAL>")"       => (Tokens.RRBR(!Pos.lno,!Pos.lno));
<INITIAL>"]"       => (Tokens.RSQBR(!Pos.lno,!Pos.lno));
<INITIAL>";"       => (Tokens.SEMICOLON(!Pos.lno,!Pos.lno));
<INITIAL>"~"       => (Tokens.TILDE(!Pos.lno,!Pos.lno));
<INITIAL>"_"       => (Tokens.UNDERSCORE(!Pos.lno,!Pos.lno));
<INITIAL>"[!"      => (Tokens.CASE(!Pos.lno,!Pos.lno));
<INITIAL>"!]"      => (Tokens.ENDCASE(!Pos.lno,!Pos.lno));

<INITIAL>{infsym}  => (
   (case Infix.infix_data yytext of 
     (Infix.LAssoc,n) => (Utils.ListUtil.nth INFIX_Ls n) (yytext,!Pos.lno,!Pos.lno)
  |  (Infix.RAssoc,n) => (Utils.ListUtil.nth INFIX_Rs n) (yytext,!Pos.lno,!Pos.lno)
  |  (_,_) 	      => Tokens.INFIX_UNREGD(yytext,!Pos.lno,!Pos.lno)));

<INITIAL>{digit}+     => (Tokens.INT (mkInt yytext,!Pos.lno,!Pos.lno));

<INITIAL>"+"{digit}+  =>
       (Tokens.RELINT ((false,mkInt (substring (yytext,1,size(yytext)-1))),!Pos.lno,!Pos.lno));

<INITIAL>"-"{digit}+  =>
       (Tokens.RELINT ((true,mkInt (substring (yytext,1,size(yytext)-1))),!Pos.lno,!Pos.lno));

<INITIAL>"\""[^\n\"]*"\""  =>
       (Tokens.STRING (substring (yytext,1,size(yytext)-2),!Pos.lno,!Pos.lno));

<INITIAL>"op"{infsym} => (Tokens.ID (yytext,!Pos.lno,!Pos.lno));

<INITIAL>{alpha}+  => (case  KeyWord.find yytext
	                 of SOME tok => tok (!Pos.lno,!Pos.lno)
	                  |    	_    => Tokens.ID (yytext,!Pos.lno,!Pos.lno));

<INITIAL>{alpha}({alpha}|{digit}|"_"|"'")* => (Tokens.ID (yytext,!Pos.lno,!Pos.lno));

<INITIAL>.         => (Pos.errmsg "Lego lexer"
	                      ("ignoring bad character "^yytext,!Pos.lno,!Pos.lno); 
                       lex());

<C>{commentopen}   => (incCL(); 
		       lex());

<C>{commentclos}   => (decCL();
			if (iszCL()) then YYBEGIN INITIAL else ();
		       lex());

<C>\n		   => (Pos.inc_lno(); lex());
<C>.		   => (lex());

<D>.*\n            => (Pos.inc_lno(); YYBEGIN INITIAL; lex());

