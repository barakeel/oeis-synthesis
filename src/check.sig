signature check =
sig

  type ('a,'b) dict = ('a,'b) Redblackmap.dict
  type prog = kernel.prog
  type anum = bloom.anum
  
  (* merge directory *)
  val init_merge : unit -> unit
  val mergedir : string
  val mergen : int ref

  val merge_itsol : (anum * (int * prog) list) list -> 
                    (anum * (int * prog) list) list
  val checkinit : unit -> unit
  val checkonline : prog * exec.exec -> unit
  val checkfinal : unit -> (anum * (int * prog) list) list
  val checkpl : prog list -> (anum * (int * prog) list) list
  val collect_candidate : unit -> prog list
  
  (* parallelization *)
  val checkspec : (unit, string, (anum * (int * prog) list) list)
    smlParallel.extspec
  val write_gptsol : string -> (anum * (int * prog) list) list -> unit
  val parallel_check : string -> unit
 
end
