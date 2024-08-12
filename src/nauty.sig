signature nauty =
sig

  type mat = int Array2.array
  
  val normalize_nauty : mat -> mat
  val normalize_nauty_wperm : mat -> mat * int list
  val normalize_nauty_wpart : int list list -> mat -> mat
  val all_inst_wperm : IntInf.int -> (IntInf.int * int list) list
  
  val normalize_hadamard : mat -> mat
  val zip_hadamard : mat -> IntInf.int
end
