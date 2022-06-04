signature human =
sig

  type prog = kernel.prog

  val humanf : prog -> string
  val human_python : int -> prog -> string
  val rm_par : string -> string
  val sexpr : prog -> string
  val parse_human : string -> prog
  
end
