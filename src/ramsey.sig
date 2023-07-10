signature ramsey =
sig

  type mat = int Array2.array
  val mat_sub : mat * int * int -> int 
  val mat_size : mat -> int
  val random_shape : int -> int -> mat
  val random_shape_nocycle : int -> int -> mat
  val edgecl_to_mat : ((int * int) * int) list -> mat
  val read_shape : string -> mat * mat
  val search : int -> int option * Time.time option -> (mat * mat) -> mat list
  val search_order : int -> (int * int) list
  val search_each_size : int option * Time.time option -> 
    (mat * mat) -> (bool * int)
  val run : string -> int option * Time.time option -> (bool * int) list
  
  val init_shape : int Array2.array -> int Array2.array list * int
  val supershapes : mat list * int -> bool array
  val normalize_naively : mat -> mat
  
end
