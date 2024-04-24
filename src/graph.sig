signature graph =
sig

  type mat = int Array2.array
  type coloring = ((int * int) * int) list
  (* colors *)
  val blue : int
  val red : int
  
  (* array2 shortcuts *)
  val mat_size : mat -> int
  val mat_sub : mat * int * int -> int
  val mat_update_sym : mat * int * int * int -> unit
  val mat_tabulate : int * (int * int -> int) -> mat
  val mat_traverse : (int * int * int -> unit) -> mat -> unit
  val mat_copy : mat -> mat
  
  (* comparison functions *)
  val edge_compare : (int * int) * (int * int) -> order
  val mat_compare : mat * mat -> order
  val mat_eq : mat -> mat -> bool
  val mat_compare_fixedsize : int -> mat * mat -> order
  val mat_set : mat list -> mat list
  
  (* I/O *)
  val zip_mat : mat -> IntInf.int
  val unzip_mat : IntInf.int -> mat
  val szip_mat : mat -> string
  val sunzip_mat : string -> mat
  val zip_full : mat -> IntInf.int
  val unzip_full : int -> IntInf.int -> mat
  val unzip_full_edgecl : int -> IntInf.int -> ((int * int) * int) list
  
  (* debug *)
  val string_of_edgel : (int * int) list -> string
  val string_of_edgecl : ((int * int) * int) list -> string
  val string_of_graph : mat -> string
  val string_of_bluegraph : mat -> string
  val string_of_mat : mat -> string
  val print_mat : mat -> unit
  
  (* matrices *)
  val mat_empty : int -> mat
  val random_mat : int -> mat
  val random_full_mat : int -> mat
  val matK : int -> mat
  val diag_mat : mat -> mat -> mat
  val extend_mat : mat -> int -> mat
  
  (* mat_permute: can also be used to reduce the size of the graph *)
  val mat_permute : mat * int -> (int -> int) -> mat
  val mk_permf : int list -> (int -> int)
  val invert_perm : int list -> int list
  val symmetrify : mat -> mat
  val permutations : 'a list -> 'a list list
  val random_subgraph : int -> mat -> mat
   
  (* neighbors *)
  val neighbor_of : int -> mat -> int -> int list
  val commonneighbor_of : int -> mat -> int * int -> int list
  val inneighbor_of : int -> mat -> int -> int list
  
  (* properties *)
  val number_of_edges : mat -> int
  val number_of_holes : mat -> int
  val all_holes : mat -> (int * int) list
  val number_of_blueedges : mat -> int
  val all_cedges : mat -> (int * int) list
  val all_edges : int -> (int * int) list
  val is_ramsey : (int * int) -> mat -> bool
  
  (* converting from matrix representation to list of edges *)
  val mat_to_edgecl : mat -> coloring
  val edgecl_to_mat : int -> coloring -> mat
  
  (* applying colorings *)
  val all_coloring : (int * int) list -> coloring list
  val apply_coloring : mat -> coloring -> mat
  
  
   
end
