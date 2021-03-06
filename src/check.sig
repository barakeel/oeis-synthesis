signature check =
sig

  type ('a,'b) dict = ('a,'b) Redblackmap.dict
  type prog = kernel.prog
  type anum = bloom.anum
  
  val merge_itsol : (anum * (int * prog) list) list -> 
                    (anum * (int * prog) list) list
  val checkinit : unit -> unit
  val checkonline : prog * exec.exec -> unit
  val checkfinal : unit -> (anum * (int * prog) list) list

end
