signature macro =
sig

  type prog = kernel.prog
  type macro = int list
  
  val random_macro : int -> macro
  val collect_prog_standalone : macro -> (kernel.prog * macro) list
  
end
