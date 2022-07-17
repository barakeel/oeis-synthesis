signature exec =
sig

  type prog = kernel.prog
  
  val large_arb : Arbint.int -> bool
  val coverp_oeis : prog -> int list * (int * int option) * int list
  val coverp_target : prog -> Arbint.int list -> bool * int
  val penum : prog -> int -> Arbint.int list
  val penum_wtime : int -> prog -> int -> Arbint.int list
  val verify_wtime : int -> int * prog -> bool * bool 
    
end
