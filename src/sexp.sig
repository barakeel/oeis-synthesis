signature sexp =
sig

  datatype sexp = Atom of string | Sexp of sexp list  
  val string_to_sexp : string -> sexp
  val sexp_to_string : sexp -> string
  
end
