signature check =
sig

  type ('a,'b) dict = ('a,'b) Redblackmap.dict
  type prog = kernel.prog
  type anum = bloom.anum
  
  val seqd: (kernel.seq, (int * prog)) dict ref
  val prnnd : (prog, real) dict ref
  
  (* functions used in search.sml and rl.sml *)
  val checkinit : unit -> unit
  val checkonline : real -> prog * exec.exec -> unit
  val checkfinal : unit -> (anum * (int * prog) list) list
  
  (* other functions *)
  val checkpl : prog list -> (anum * (int * prog) list) list
  val checkpl_target : anum -> prog list -> 
    (int * (anum * (int * prog) list) list)
  val collect_candidate : unit -> prog list
  
  (* merge directory *)
  val init_merge : unit -> unit
  val mergedir : string
  val mergen : int ref
  val merge_itsol_default : string -> (anum * (int * prog) list) list
  
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
 
  (* hanabi experiment *)
  val checkinit_hanabi : unit -> unit
  val checkonline_hanabi : prog -> unit
  val checkfinal_hanabi : unit -> kernel.hanabi list
  val merge_hanabi : string option -> kernel.hanabi list
 
  (* arcagi experiment *)
  val checkinit_arcagi : unit -> unit
  val checkonline_arcagi : prog -> unit
  val checkfinal_arcagi : unit -> kernel.arcagi list
  val compare_arcagi : (prog * bool * int) * (prog * bool * int) -> order
  val merge_arcagi : kernel.arcagi list -> string option -> kernel.arcagi list

  (* matchback experiment *)
  val checkinit_matchback : unit -> unit
  val checkonline_matchback : prog -> unit
  val checkfinal_matchback : unit -> (kernel.seq * prog) list



  (* standard checking *)
  val check_wind : (int, (int * prog) list) dict ref ->
    prog * (int * int) list -> unit

  (* statistics *)
  val stats_dir : string ->
    (anum * (int * prog) list) list -> 
    (anum * (int * prog) list) list -> unit

end
