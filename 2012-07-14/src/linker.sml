(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

(* 
   $Log: linkOpen.sml,v $
   Revision 1.10  1998/11/10 15:28:44  ctm
   ConorInductiveNeeds now uses Quartermaster

   Revision 1.9  1998/10/30 14:14:04  ctm
   quartermaster added

   Revision 1.8  1997/11/24 11:01:29  tms
   merged immed-may-fail with main branch

   Revision 1.7.2.3  1997/10/13 16:47:10  djs
   More problems with the above.

   Revision 1.7.2.2  1997/10/13 16:21:28  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.7.2.1  1997/10/10 17:02:31  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.7  1997/05/08 13:54:10  tms
   Generalised Expansion Mechanism to Cope with Path information
  
   Revision 1.6  1997/03/06 09:53:14  tms
   restructured module Pbp
  
   Revision 1.5  1997/02/17 17:40:26  tms 
   integrated error handler in tactics functor
*)

structure Context=FunContext (
	  structure Term=Term )

structure LegoFormat=FunLegoFormat (
	  structure Term=Term )

structure Error=FunError (
	  structure Term=Term
	  structure LegoFormat=LegoFormat ) 

structure Pretty=FunPretty (
	  structure Term=Term
	  structure Context=Context
	  structure LegoFormat=LegoFormat ) 

structure Subst=FunSubst (
	  structure Term=Term
	  structure Context=Context
	  structure Pretty=Pretty ) 

structure UMopen=FunUMopen (
	  structure Term=Term
	  structure Subst=Subst
	  structure LegoFormat=LegoFormat  
	  structure Pretty=Pretty ) 

structure Abst=FunAbst (
	  structure Term=Term
	  structure UMopen=UMopen
	  structure Pretty=Pretty ) 

structure Toc=FunToc (
	  structure Term=Term
	  structure Subst=Subst
	  structure UMopen=UMopen
	  structure Pretty=Pretty ) 

structure Unif=FunUnif (
	  structure Term=Term
	  structure Subst=Subst
	  structure UMopen=UMopen
	  structure Toc=Toc 
	  structure Pretty=Pretty ) 

structure ParTm=FunParTm (
	  structure Subst=Subst
	  structure UMopen=UMopen
	  structure Unif=Unif 
	  structure Pretty=Pretty ) 

structure Machine=FunMachine (
	  structure Term=Term 
	  structure Context=Context 
	  structure Subst=Subst 
	  structure UMopen=UMopen 
	  structure Abst=Abst 
	  structure Toc=Toc 
	  structure ParTm=ParTm 
	  structure Pretty=Pretty 
	  structure Error=Error )

structure Expand =FunExpand (
	  structure Term=Term 
	  structure Subst=Subst 
	  structure Error=Error )

structure UndoKnots=FunConorKnots(UndoKnotTypes) (* CONORKNOTTYPES !!! *)

structure Namespace=FunNamespace (
	  structure Term=Term 
	  structure Context=Context 
	  structure Subst=Subst 
	  structure UMopen=UMopen 
	  structure Expand=Expand
	  structure ParTm=ParTm 
	  structure UndoKnots=UndoKnots
	  structure Machine=Machine
	  structure Pretty=Pretty )

structure Concrete=FunConcrete(
	  structure Term=Term 
	  structure Context=Context 
	  structure Subst=Subst 
	  structure UMopen=UMopen 
	  structure Toc=Toc 
	  structure Unif=Unif 
	  structure ParTm=ParTm 
	  structure Machine=Machine
	  structure Pretty=Pretty )

structure Engine=FunConstructiveEngine (
	  structure Term=Term 
	  structure Concrete=Concrete 
	  structure Namespace=Namespace )

structure Pbp=FunPbp (
	  structure LegoFormat=LegoFormat
	  structure PbpInput=FunPbpInput (
	  	    structure LegoFormat=LegoFormat
		    structure Engine=Engine
	  	    structure Namespace=Namespace)
		    ) 

structure Synt = FunSynt (
	  structure Term=Term 
	  structure Subst=Subst 
	  structure UMopen=UMopen 
	  structure Toc=Toc 
	  structure ParTm=ParTm 
	  structure Namespace=Namespace
	  structure Engine=Engine
	  structure Pretty=Pretty )

structure Toplevel = FunToplevel (
	  structure Term=Term 
	  structure Subst=Subst 
	  structure UMopen=UMopen 
	  structure ParTm=ParTm 
	  structure Namespace=Namespace
	  structure Engine=Engine
	  structure Synt=Synt
	  structure Pretty=Pretty
	  structure Error=Error ) (* 2011: added for Immed/Assumption *)

structure Inductive = FunInductive (
	  structure Term=Term 
	  structure Concrete=Concrete
	  structure Namespace=Namespace )

structure QuarterMaster=FunQuarterMaster (
	  structure Term=Term 
	  structure Concrete=Concrete
	  structure Namespace=Namespace
	  structure Engine=Engine
	  structure Pretty=Pretty )

structure ConorInductiveNeeds = FunConorInductiveNeeds(
	  structure Term=Term 
	  structure UMopen=UMopen 
	  structure Toc=Toc 
	  structure Namespace=Namespace
	  structure Engine=Engine
	  structure QuarterMaster=QuarterMaster)

structure ConorInductive = FunConorInductive (
	  structure Engine=Engine
	  structure ConorInductiveNeeds=ConorInductiveNeeds
	  structure Pretty=Pretty )

structure Top = FunTop (
	  structure Term=Term 
	  structure Subst=Subst 
	  structure UMopen=UMopen 
	  structure ParTm=ParTm 
	  structure Toplevel=Toplevel
	  structure Concrete=Concrete
	  structure Namespace=Namespace
	  structure Engine=Engine
	  structure Inductive=Inductive
	  structure ConorInductive=ConorInductive
	  structure Expand=Expand
	  structure Pretty=Pretty )

structure Discharge = FunDischarge (
	  structure Term=Term 
	  structure Context=Context 
	  structure Subst=Subst 
	  structure ParTm=ParTm 
	  structure Namespace=Namespace
	  structure Engine=Engine )
	  
structure Modules = FunModules (
	  structure Term=Term 
	  structure Context=Context 
	  structure Top=Top
	  structure Toplevel=Toplevel
	  structure Namespace=Namespace 
	  structure Pretty=Pretty )

structure Tactics = FunTactics (
	  structure Term=Term 
	  structure Subst=Subst 
	  structure UMopen=UMopen 
	  structure Unif=Unif 
	  structure Abst=Abst 
	  structure Toplevel=Toplevel
	  structure Namespace=Namespace
	  structure Concrete=Concrete
	  structure Engine=Engine
	  structure Pretty=Pretty 
	  structure Error=Error ) 

structure ConorTopNeeds=FunConorTopNeeds (
	  structure UMopen=UMopen 
	  structure Toc=Toc
	  structure Namespace=Namespace
	  structure Concrete=Concrete
	  structure Engine=Engine
	  structure Tactics=Tactics
	  structure Toplevel=Toplevel
	  structure ConorInductiveNeeds=ConorInductiveNeeds)

structure ConorTop=FunConorTop (
	  structure UMopen=UMopen 
	  structure Toc=Toc
	  structure Namespace=Namespace
	  structure Concrete=Concrete
	  structure Engine=Engine
	  structure ConorInductiveNeeds=ConorInductiveNeeds
	  structure ConorTopNeeds=ConorTopNeeds
	  structure Pretty=Pretty )

structure PromptKnots=FunConorKnots(PromptKnotTypes) (* CONORKNOTTYPES !!! *)

structure CTS : CONORTHENSIG=
struct
	structure PromptKnots=PromptKnots
	structure UndoKnots  =UndoKnots
end

structure ConorThen=FunConorThen(
	  structure Namespace=Namespace
	  structure CTS=CTS)


structure Init = FunInit (
	  structure Infix=Infix
	  structure UMopen=UMopen 
	  structure Namespace=Namespace
	  structure Tactics=Tactics
	  structure Toplevel=Toplevel
	  structure Top=Top
	  structure ConorThen=ConorThen)

structure Tacticals=FunTacticals (
	  structure Namespace=Namespace
	  structure ConorThen=ConorThen
	  structure Tactics=Tactics)

structure Logic=FunLogic (
	  structure Namespace=Namespace
	  structure Concrete=Concrete 
	  structure Toplevel=Toplevel
	  structure Modules=Modules) (* Modules? *) 	  	    

(* 2011: phew! *)


