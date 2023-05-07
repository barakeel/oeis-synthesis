signature exec =
sig

  type prog = kernel.prog
  type exec = IntInf.int * IntInf.int * IntInf.int -> IntInf.int
  
  
  val large_arb : IntInf.int -> bool
  val large_int : IntInf.int -> bool
  val mk_exec_move : int -> exec list -> exec
  val mk_exec : prog -> exec
  val mk_exec_onev : prog -> (IntInf.int -> IntInf.int)
  val cache_exec : exec -> exec
  val coverf_oeis : exec -> (int * int) list * int * int list
  val coverp_target : prog -> kernel.seq -> bool * int
  
  (* mostly for SMT export *)
  val penum2_list : prog -> (IntInf.int * IntInf.int) list -> kernel.seq
  val penum : prog -> int -> kernel.seq
  val penum_limit : IntInf.int -> prog -> int -> kernel.seq
  val penum_wtime : int -> prog -> int -> kernel.seq
  val verify_wtime : int -> int * prog -> bool * bool 
  val verify_eq : int * int -> prog * prog -> bool * bool
  
  (* fs experiment *)
  val create_fsf : exec -> (IntInf.int -> IntInf.int)
  (* pgen experiment *)
  val penum_pgen : exec -> (int * kernel.prog) list
  (* seq experiment *)
  val match_seq : kernel.seq -> exec -> bool * int
   
  (* parallel execution (wip) *)
  val execspec : (unit, kernel.prog list, kernel.seq list) smlParallel.extspec
  val parallel_exec : int -> string -> unit
end
