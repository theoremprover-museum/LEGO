110.81  x86    
         *   P       *      �   h��S%�����]��Y  �5;�0erho�f�V wOkO)�c8�_;~����wOkO)�c8�_;~����               n               n��S%�����]��Y�5;�0erho�f�guid-(sources.cm):help.sml-1529499815.559
  �    �"     �New Commands:
Init
  Init U                  The inconsistent system Type:Type
Undo
  Undo                    Undo most recent tactical (equiv. to Undo 1)
  UndoAll                 Undo back to top-level goal
Configuration
  Configure Equality      sets up the equality to be used by
    ID1 ID2 ID3             Qrepl, Theorems, Inversion, Induction and Qnify
                            where ID1 is the name of the equality predicate,
                                  ID2 is the name of its reflexivity proof and
                                  ID3 is the name of its substitutivity proof
  Configure Infix S A P   introduces a new infix operator S with
                            priority P and associativity A.
                              S ::= + | - | / | * | << | >> | /\ | \/
                                      | |- | :: | &ID | @ID
                              A ::= left | right
                              P ::= 1..9
Induction
  Induction ID            do induction on premise ID
  Induction NUM           do induction on NUM unnamed premise
  Induction TERM          abstract TERM from the goal, then do induction on it
Unification Problems
  Qnify NUM               considers leftmost NUM equational premises
  Qnify                   considers all equational premises
  Qnify ID                equivalent to Refine cut ID; Qnify 1
User-defined Tactics
  UTac ID                 executes the tactic ID
                          To add new tactics, use legoML and invoke Drop;
                          to enter the ML level. You can add any function
                          f:unit->unit via Tactics.add_tactic ID f;
                          The command lego() will return you to the LEGO level
                          Recall that you can save such extensions via
                          ExportState
Miscellaneous
  Assumption [NUM]        attempts to close goal NUM by an assumption
  Invert ID               invert ID
Tacticals
  -> Notice that backtracking is only possible in a proof state!
  EXPRSN1 Then EXPRSN2    evaluate EXPRSN1, if evaluation succeeds,
                            evaluate EXPRSN2 on all subgoals
  EXPRSN1 Else  EXPRSN2   evaluate EXPRSN1, if evaluation fails,
                            backtrack and evaluate EXPRSN2
  For n EXPRSN            evaluate EXPRSN Then EXPRSN Then ... (n times)
  Repeat EXPRSN           evaluate EXPRSN Then EXPRSN Then ... and backtrack
                            last failure
  Succeed                 this tactical doesn't do anything
  Fail                    this tactical always fails
  Try EXPRSN              evaluate EXPRSN and backtrack if evaluation fails
  (EXPRSN)                evaluate EXPRSN

Inductive declarations
  Inductive DECLS1        defines datatype(s) DECLS1 with constructors
    [Relation]            inductive relation
    [Inversion]           generate inversion theorem
    [Theorems]            proves some properties for *some* inductive declarations
    [ElimOver U]          the generated elimination rule constructs objects of type U (the default is TYPE)
    [Double]              generate nested double elimination rule
    [Parameters  DECS]         
    Constructors DECLS2        
    [NoReductions]        prevent generation of computation rules
Module concept
  Module ID               start a module named ID which requires modules
    [Import ID1 ID2 ..]        named ID1 ID2 ..
  Make ID                 process module ID
Basic Commands:
  Init TT[']              where TT is LF, PCC, CC, or XCC
      The optional ' requests maximal universe polymorphism.
  Goal [ID :] TERM        start named refinement proof with goal TERM
  Refine [NUM] TERM       refine goal NUM by TERM
  Intros [NUM] ID1 ID2 .. Pi-introductions on HNF of goal NUM
  intros [NUM] ID1 ID2 .. Pi-introductions on goal NUM
  Claim TERM              create a new goal (lemma) in a proof
  Equiv TERM              replace first goal with equivalent goal TERM
  Qrepl TERM              use the type of TERM as a conditional equation
                               to rewrite the current goal
  Prf                     show current proof state
  Save [ID]               save proof term as global with name ID
  $Save [ID]              save proof term as local with name ID
  KillRef                 kill the current refinement proof
  Discharge ID            discharge assumptions back to ID
  Help                 print this message
  Pwd                  print working directory
  Cd "STRING"          change directory
  Ctxt [n]             prints all (last n) context entries
  Decls [n]            prints all (last n) declarations (not definitions)
Basic Syntax: (some theories don't have 'Type' or Sigma)
  TERM ::= Prop | Type                     kinds
         | ID                              variable or constant
         | {x:TERM}TERM | TERM -> TERM     Pi
         | [x:TERM]TERM                    Lambda
         | TERM TERM                       application
         | TERM.TERM                       postfix application
         | TERM SYM TERM                   infix application
         | <x:TERM>TERM | TERM # TERM      Sigma
         | (TERM,TERM, ...)                tuple
         | (TERM,TERM,...:TERM)            annotated tuple
         | TERM.1 | TERM.2                 projections
         | (TERM : TERM)                   typecast
         | [x=TERM]TERM                    'let'
  CXT  ::= [] | CXT BIND                   context
  BIND ::= [x:TERM]                        local variable or assumption
         | [x=TERM]                        global definition
         | $[x:TERM]                       global variable or assumption
         | $[x=TERM]                       local definition
   *** There is much more info on the WWW
         http://www.dcs.ed.ac.uk/home/lego    ***	       	   �   �    �D$H� �D$;|$wA��  �D$�@T�G�E �G�m�E �G�G�   �o�o�G�   �G�G�o�� ���3�;|$w*�D$L�t$P�L$T�H�1�@�(�t$H�L$L�t$P�L$T�d$H� �T$ �d$H��help.sml   1p�Help"5DCA nff1pa"help"4aAnC"->"2��Bp"�5;�0erho�f�" aCC�unit" aE000���?00��0�$ 00sABi1�A 1aB