signature ramsey =
sig

  type mat = int Array2.array
  val mat_sub : mat * int * int -> int 
  val mat_size : mat -> int

  val continue_flag : bool ref
  val shuffle_flag : bool ref
  
  
  (* random shapes *)
  val random_mat : int -> mat
  val random_shape : int -> int -> mat
  val random_shape_nocycle : int -> int -> mat
  val string_of_graph : mat -> string
  val string_of_shape : mat -> string
  
  (* search tools *)
  val search_order : int -> (int * int) list
  val search_order_linear : int -> (int * int) list
  val edgel_glob : (int * int) list ref
  val subsets_of_size : int -> int list -> int list list
  
  (* normalization *)
  val normalize_nauty : mat -> mat
  val normalize_nauty_safe : mat -> mat
  
  (* properties *)
  val is_ackset : mat -> bool
  val is_ackset_pb : (mat * mat) -> bool
  val not_automorphic : mat -> bool
  val not_automorphic_pb : (mat * mat) -> bool
  
  (* cycles *)
  val has_cycle : int -> mat -> bool
  
  (* keeps only one color *)
  val keep_only : int -> mat -> mat
  
  (* problems *)
  val read_cnf : string -> ((mat * mat) * bool)
  val string_of_pbr : ((mat * mat) * bool) * (bool * int) -> string
  
  (* shapes and supershapes *)
  val all_undirected_shapes : int -> mat list
  val reduce_mat : mat -> mat
  val deduplicate_shapel : mat list -> mat list
  val supershapes : mat -> bool array
  val isomorphic_shapes : mat -> mat list

  (* conversion between formats *)
  val edgecl_to_mat : ((int * int) * int) list -> mat
  val mat_to_edgecl : mat -> ((int * int) * int) list
  val mat_to_edgecl_undirected : mat -> ((int * int) * int) list
  val shape_to_int : mat -> int
  val zip_mat : mat -> IntInf.int
  val unzip_mat : IntInf.int -> mat
 
  (* problems *)
  val create_pbl : int -> ((mat * mat) * (mat * mat) list) list
  val create_pbl_same : int -> ((mat * mat) * (mat * mat) list) list
  val create_pbl_undirected : int -> ((mat * mat) * bool) list

  (* main *)
  val search_each_size : ((mat * mat) * bool) -> (bool * int)
  val search_one_size : int -> ((mat * mat) * bool) -> (bool * int)
  
  (* parallel *)
  val ramseyspec : 
    (unit, ((mat * mat) * bool), (bool * int)) smlParallel.extspec 
  val parallel_ramsey : 
    int -> string -> ((mat * mat) * bool) list -> 
      (((mat * mat) * bool) * (bool * int)) list
  
end
