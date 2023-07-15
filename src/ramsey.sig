signature ramsey =
sig

  type mat = int Array2.array
  val mat_sub : mat * int * int -> int 
  val mat_size : mat -> int
  val random_mat : int -> mat
  val random_shape : int -> int -> mat
  val random_shape_nocycle : int -> int -> mat
  val edgecl_to_mat : ((int * int) * int) list -> mat
  val read_shape : string -> mat * mat
  val search_order : int -> (int * int) list
  
  val subsets_of_size_faster : int -> int list * int -> int list list
  
  (* normalization *)
  val normalize_naively : mat -> mat
  val equitable_partition : mat -> int list list list
  
  (* projection *)
  val keep_only : int -> mat -> mat
  
  (* shapes *)
  val isomorphic_shapes : mat -> mat list * int
  val supershapes_one_aux : int -> ((int * int) * int) list -> int list
  val supershapes_one : int -> mat -> int list
  val supershapes : mat -> bool array
  val all_shapes : unit -> mat list
  val normalize_shapes : mat list -> (int * mat) list
  val compute_write_supershapes : (int * mat) list -> unit
  val propshapes : mat -> (int * int) list array
  val compute_write_propshapes : (int * mat) list -> unit
  (* conversion between formats *)
  val mat_to_edgecl : mat -> ((int * int) * int) list
  val mat_to_edge1l : mat -> ((int * int) * int) list
  val read_prop : string -> (int * int) list array

  (* main *)
  val search_each_size : (mat * mat) -> (bool * int)
  val run : string -> (bool * int) list

  (* parallel *)
  val ramseyspec : (unit, string, (bool * int)) smlParallel.extspec
  val parallel_ramsey : 
    int -> string -> string list -> (string * (bool * int)) list
  
end
