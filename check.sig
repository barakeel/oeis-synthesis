signature check =
sig

  type ('a,'b) dict = ('a,'b) Redblackmap.dict
  type prog = kernel.prog
  type anum = bloom.anum
  
  val merge_isol : (anum * prog) list -> (anum * prog) list
  val check : prog list -> (anum * prog) list

  (* alternative memory less way *)
  val checkinit : unit -> unit
  val checkonline : prog -> unit
  val checkfinal : unit -> (int * kernel.prog) list

end
