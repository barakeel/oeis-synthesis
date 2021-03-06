signature exec =
sig

  type prog = kernel.prog
  type exec = IntInf.int * IntInf.int * IntInf.int -> IntInf.int
  
  val large_arb : IntInf.int -> bool
  val mk_exec_move : int -> exec list -> exec
  val mk_exec : prog -> exec
  val mk_exec_onev : prog -> (IntInf.int -> IntInf.int)
  val cache_exec : exec -> exec
  val coverf_oeis : exec -> (int * int) list * int * int list
  val coverp_target : prog -> kernel.seq -> bool * int
  val penum : prog -> int -> kernel.seq
  val penum_limit : IntInf.int -> prog -> int -> kernel.seq
  val penum_wtime : int -> prog -> int -> kernel.seq
  val verify_wtime : int -> int * prog -> bool * bool 
    
end
