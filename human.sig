signature human =
sig

  type prog = kernel.prog

  val polynorm_flag : bool ref
  val humanf : prog -> string
  val humani : int -> prog -> string
  val rm_par : string -> string
  val sexpr : prog -> string
  val parse_human : string -> prog
  
end
