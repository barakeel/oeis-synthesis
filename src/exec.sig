signature exec =
sig

  type prog = kernel.prog
  type exec = IntInf.int * IntInf.int * IntInf.int -> IntInf.int
  
  val large_arb : IntInf.int -> bool
  val mk_exec_move : int -> exec list -> exec
  val mk_exec : prog -> exec
  val mk_exec_onev : prog -> (IntInf.int -> IntInf.int)
  val cache_exec : exec -> exec
  val coverf_oeis : exec -> int list * (int * int option) * int list
  val coverp_target : prog -> IntInf.int list -> bool * int
  val penum : prog -> int -> IntInf.int list
  val penum_wtime : int -> prog -> int -> IntInf.int list
  val verify_wtime : int -> int * prog -> bool * bool 
    
end
