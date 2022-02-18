signature kolmo =
sig

  include Abbrev

  type seq = kernel.seq
  type prog = kernel.prog
  type progi = kernel.progi
  type exec = kernel.exec
  
  val quotient_flag : bool ref

  (* kolmogoroff search *)
  val seld : (int, progi vector) Redblackmap.dict ref
  val winl : prog list ref
  val kolmo : int -> unit
  
  (* stats *)
  val stats : unit -> unit
  val div_counter : int ref
  val sem_counter : int ref

end
