(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* build phase: link and load *)

structure Pos:POS = 
  Pos(structure Printing=Printing)

structure LegoLrVals:Lego_LRVALS =
  LegoLrValsFun(structure Token = LrParser.Token
		structure Pos = Pos
		structure Term = Term
		structure Concrete = Concrete
		structure Namespace = Namespace
		structure Engine = Engine
		structure Modules = Modules
		structure Logic = Logic
		structure Top = Top
		structure Tactics = Tactics
		structure Tacticals = Tacticals
		structure Toplevel = Toplevel
		structure Discharge = Discharge
		structure Init = Init
                (* structure Infix = Infix *) 
		structure ConorTop = ConorTop
		structure ConorThen = ConorThen
                structure QuarterMaster = QuarterMaster
                structure Pbp = Pbp
		structure Pretty = Pretty
		structure Error = Error
		)

structure LegoLex:LEXER =
  LegoLexFun(structure Tokens = LegoLrVals.Tokens
	     structure Pos = Pos
             structure Infix = Infix)

structure LegoParser:PARSER =
  Join(structure Lex = LegoLex
       structure LrParser = LrParser
       structure ParserData = LegoLrVals.ParserData)
  
