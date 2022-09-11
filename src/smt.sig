signature smt =
sig

  type prog = kernel.prog
  val export_smt2 : bool -> string -> string -> unit
  
end
