signature exec_pow =
sig
  
  type prog = kernel.prog
  type exec = IntInf.int -> IntInf.int
  val mk_exec : prog -> exec
  
end
