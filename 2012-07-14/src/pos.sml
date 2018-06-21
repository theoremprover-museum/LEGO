(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* The "abstract type" of lexer positions *)
signature POS =
  sig
    type pos
    val lno : pos ref
    val init_lno : unit->unit
    val inc_lno : unit->unit
    val errmsg : string->(string*pos*pos)->unit
  end;

functor Pos(structure Printing:PRINTING) : POS =
  struct
    type pos = int
    val lno = ref 0
    fun init_lno() = lno:=1
    fun inc_lno() = lno:=(!lno)+1
    fun errmsg who (msg,line:pos,_:pos) =
      Printing.message(who^"; line "^(Int.toString line)^": "^msg)
  end;

