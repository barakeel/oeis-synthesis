signature nauty =
sig

  type mat = int Array2.array
  
  val normalize_nauty : mat -> mat
  val normalize_nauty_wperm : mat -> mat * int list
  val all_inst_wperm : IntInf.int -> (IntInf.int * int list) list
  
end
