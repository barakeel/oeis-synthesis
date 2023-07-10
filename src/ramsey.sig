signature ramsey =
sig

  type mat = int Array2.array
  val mat_sub : mat * int * int -> int 
  val random_shape : int -> int -> mat
  val random_shape_nocycle : int -> int -> mat
  val edgecl_to_mat : ((int * int) * int) list -> mat
  val read_shape : string -> mat * mat
  val search : int -> int -> (mat * mat) -> mat list
  val search_each_size : int -> (mat * mat) -> (bool * int)
  val run : string -> int -> (bool * int) list
  
end
