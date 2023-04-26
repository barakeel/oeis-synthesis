signature exec_intl =
sig

  type prog = kernel.prog
  type exec = IntInf.int list * IntInf.int list * IntInf.int list -> 
    IntInf.int list
  
  val mk_exec_move : int -> exec list -> exec
  val mk_exec : prog -> exec
  val coverf_oeis : exec -> (int * int) list * int * int list
  val verify_wtime : int -> int * prog -> bool * bool 
  
end
