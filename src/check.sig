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
  val checkpl : prog list -> (anum * (int * prog) list) list
  val checkpl_slow : prog list -> (anum * (int * prog) list) list
  
  val collect_candidate : unit -> prog list
  
  val checkinit_prime : unit -> unit
  val checkonline_prime : prog * exec.exec -> exec.exec
  val checkfinal_prime : unit -> (kernel.seq * (int * prog)) list
  val merge_primesol : (kernel.seq  * (int * prog)) list -> 
    (kernel.seq * (int * prog)) list

end
