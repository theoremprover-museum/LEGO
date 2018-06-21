(* ********************************************************** * 
   port to NJ-SML 110: James McKinna 24 Nov 2008--11 Nov 2011

   ********************************************************** *)

signature PRINTING = 
  sig
    val prts : TextIO.outstream -> string -> unit
    val prti : TextIO.outstream -> int -> unit
    val prtb : TextIO.outstream -> bool -> unit
    val prtnl : TextIO.outstream -> unit
    val prtsp : TextIO.outstream -> unit
    val prs : TextIO.vector -> unit
    val pri : int -> unit
    val prb : bool -> unit
    val prnl : unit -> unit
    val prsp : unit -> unit
    val flout : unit
    val message : string -> unit
    val loudmessage : string -> unit
    val errmsg : string -> unit
    val flerr : unit
    val SetAnnotating : bool -> unit
  end

structure Printing : PRINTING = 
struct
(* printing *)
 local	(* open TextIO *)   

  val outp     = TextIO.output
  val std_out  = TextIO.stdOut
  val std_err  = TextIO.stdErr
  fun flsh out = TextIO.flushOut out

  fun prtmsg out s = Format.prtmsg out s

 in 

  fun prts  out s = outp(out,s)
  fun prti  out i = prts out (Int.toString i)
  fun prtb  out b = prts out (Bool.toString b)
  fun prtnl out   = prts out "\n"
  fun prtsp out   = prts out Utils.StringUtil.spaceString

  val prs     = prts std_out 
  val pri     = prti std_out 
  val prb     = prtb std_out 
  fun prnl()  = prtnl std_out
  fun prsp()  = prtsp std_out
  val flout   = flsh std_out

  val message = prtmsg std_out
  fun loudmessage s = message (Annotate.stringAnnotating s) 

  val errmsg  = prtmsg std_err
  val flerr   = flsh std_err

  fun SetAnnotating isActive =
      (Annotate.setAnnotating isActive;
       message ("Annotating is now "^
		(if isActive then "enabled" else "disabled")))

 end (* local *)
end; (* struct *)

