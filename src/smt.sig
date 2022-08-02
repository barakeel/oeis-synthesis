signature smt =
sig

  type prog = kernel.prog
  val smttop : string -> prog -> string list
  val export_smt2 : bool -> string -> (string * 'a * prog * prog) list -> unit
  
end
