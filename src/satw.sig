signature satw =
sig

  type mat = int Array2.array
  type coloring = ((int * int) * int) list
  val wsolve : int -> int * int -> mat list
  
  val lemmal : ((mat * int list) * coloring option) list ref
  val wglue : mat * mat -> int list list -> int * int -> mat list
  
end
