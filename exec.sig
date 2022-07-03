signature exec =
sig

  type prog = kernel.prog
  
  val large_arb : Arbint.int -> bool
  val coverp_oeis : prog -> int list * (int * real option) * int list
  val coverp_target : prog -> Arbint.int list -> bool * int
  val penum : prog -> int -> Arbint.int list
  val penum_wtime : real -> prog -> int -> Arbint.int list
  val verify_wtime : real -> int * prog -> bool * bool 
    
end
