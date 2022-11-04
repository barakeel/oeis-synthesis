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
  val collect_candidate : unit -> prog list
  
  (* primes *)
  val checkinit_prime : unit -> unit
  val checkonline_prime : prog * exec.exec -> exec.exec
  val checkfinal_prime : unit -> (kernel.seq * (int * prog)) list
  val merge_primesol : (kernel.seq  * (int * prog)) list -> 
    (kernel.seq * (int * prog)) list

  (* hadamard *)
  val checkinit_hdm : unit -> unit
  val checkonline_hdm : prog * exec.exec -> unit
  val checkfinal_hdm : unit -> (kernel.seq * (int * prog)) list
  val merge_hdmsol : (kernel.seq  * (int * prog)) list -> 
    (kernel.seq * (int * prog)) list

  (* parallelization *)
  val checkspec : (unit, string, (anum * (int * prog) list) list)
    smlParallel.extspec
  val write_gsol : string -> (anum * (int * prog) list) list -> unit
  val parallel_check : string -> unit
  
end
