signature check =
sig

  type ('a,'b) dict = ('a,'b) Redblackmap.dict
  type prog = kernel.prog
  type anum = bloom.anum
  
  val merge_isol : (anum * prog) list -> (anum * prog) list
  val checkinit : unit -> unit
  val checkonline : prog * exec.exec -> unit
  val checkfinal : unit -> (int * prog) list

end