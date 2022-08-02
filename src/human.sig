signature human =
sig

  type prog = kernel.prog
  datatype sexp = Sexp of sexp list | Stoken of string
  
  val humanf : prog -> string
  val human_python : int -> prog -> string
  val rm_par : string -> string
  val parse_sexp : string -> sexp
  val sexpr : prog -> string
  val parse_human : string -> prog
  val parse_prog : string -> prog
  
end
