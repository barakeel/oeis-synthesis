signature check =
sig

  type ('a,'b) dict = ('a,'b) Redblackmap.dict
  type prog = kernel.prog
  type anum = bloom.anum
  
  (* functions used in search.sml and rl.sml *)
  val checkinit : unit -> unit
  val checkonline : real -> prog * exec.exec -> unit
  val checkfinal : unit -> (anum * (int * prog) list) list
  
  (* other functions *)
  val checkpl : prog list -> (anum * (int * prog) list) list
  val collect_candidate : unit -> prog list
  
  (* merge directory *)
  val init_merge : unit -> unit
  val mergedir : string
  val mergen : int ref

  (* external parallelization *)
  val merge_itsol : (anum * (int * prog) list) list -> 
                    (anum * (int * prog) list) list
  val checkspec : (unit, string, (anum * (int * prog) list) list)
    smlParallel.extspec
  val write_gptsol : string -> (anum * (int * prog) list) list -> unit
  val parallel_check : string -> unit
 
  (* pgen experiment *)
  val checkinit_pgen : unit -> unit
  val checkonline_pgen : prog * exec.exec -> unit
  val checkfinal_pgen : unit -> kernel.pgen list
  val merge_pgen : string option -> kernel.pgen list
 
  (* ramsey experiment *)
  val checkinit_ramsey : unit -> unit
  val checkonline_ramsey : prog * exec.exec -> unit
  val checkfinal_ramsey : unit -> kernel.ramsey list
  val merge_ramsey : string option -> kernel.ramsey list
 
 
end
