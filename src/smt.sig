signature smt =
sig

  type prog = kernel.prog
  val export_smt2 : bool -> string -> (int * (prog * prog)) list -> unit
  
end
