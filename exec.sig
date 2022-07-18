signature exec =
sig

  type prog = kernel.prog
  type exec = Arbint.int * Arbint.int * Arbint.int -> Arbint.int
  
  val large_arb : Arbint.int -> bool
  val mk_exec_move : int -> exec list -> exec
  val mk_exec : prog -> exec
  val mk_exec_onev : prog -> (Arbint.int -> Arbint.int)
  val cache_exec : exec -> exec
  val coverf_oeis : exec -> int list * (int * int option) * int list
  val coverp_target : prog -> Arbint.int list -> bool * int
  val penum : prog -> int -> Arbint.int list
  val penum_wtime : int -> prog -> int -> Arbint.int list
  val verify_wtime : int -> int * prog -> bool * bool 
    
end
