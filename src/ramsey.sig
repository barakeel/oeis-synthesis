signature ramsey =
sig

  type mat = int Array2.array
  val mat_sub : mat * int * int -> int 
  val mat_size : mat -> int

  
  (* random shapes *)
  val random_mat : int -> mat
  val random_shape : int -> int -> mat
  val random_shape_nocycle : int -> int -> mat
  
  (* search tools *)
  val search_order : int -> (int * int) list
  val subsets_of_size : int -> int list -> int list list
  
  (* normalization *)
  val normalize_nauty : mat -> mat
  val normalize_nauty_safe : mat -> mat
  
  (* keeps only one color *)
  val keep_only : int -> mat -> mat
  
  (* shapes and supershapes *)
  val read_problem : string -> mat * mat
  val all_undirected_shapes : int -> mat list
  val reduce_mat : mat -> mat
  val regroup_isoshapes : mat list -> (int * mat) list
  val supershapes : mat -> bool array
  val all_shapes_from_dir : string -> mat list
  val isomorphic_shapes : mat -> mat list
  
  val write_supershapes : string -> mat list -> unit
  val read_supershapes : string -> bool array
  
  (* conversion between formats *)
  val edgecl_to_mat : ((int * int) * int) list -> mat
  val mat_to_edgecl : mat -> ((int * int) * int) list
  val shape_to_int : mat -> int
  val zip_mat : mat -> IntInf.int

  (* main *)
  val search_each_size : (mat * mat) -> (bool * int)
  val run : (mat * mat) list -> (bool * int) list
  
  (* parallel *)
  val ramseyspec : (unit, string, (bool * int)) smlParallel.extspec
  val parallel_ramsey : 
    int -> string -> string list -> (string * (bool * int)) list
  
end
