signature nauty =
sig

  type mat = int Array2.array
  
  val refine_partition : int list list -> int list list list
  val normalize_nauty : mat -> mat
  val normalize_nauty_wperm : mat -> mat * int list
  val nauty_set : mat list -> mat list
  val subgraphs : mat -> int -> mat list
  

end
