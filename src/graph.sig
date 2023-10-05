signature graph =
sig

  type mat = int Array2.array
   
  (* colors *)
  val blue : int
  val red : int
  
  (* array2 shortcuts *)
  val mat_size : mat -> int
  val mat_sub : mat * int * int -> int
  val mat_update_sym : mat * int * int * int -> unit
  val mat_tabulate : int * (int * int -> int) -> mat
  val mat_appi : (int * int * int -> unit) -> mat -> unit
  val mat_app : (int -> unit) -> mat -> unit
  val mat_copy : mat -> mat
  
  (* comparison functions *)
  val edge_compare : (int * int) * (int * int) -> order
  val mat_compare : mat * mat -> order
  val mat_compare_fixedsize : int -> mat * mat -> order
  
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
  
  (* initialization *)
  val random_mat : int -> mat
  val random_full_mat : int -> mat
  val random_shape : int -> int -> mat
  val random_shape_nocycle : int -> int -> mat
  val matK : int -> mat
   
  (* mat_permute also can also be used to reduce the size of the graph *)
  val mat_permute : mat * int -> (int -> int) -> mat
  val mk_permf : int list -> (int -> int)
  val symmetrify : mat -> mat
  val permutations : 'a list -> 'a list list
 
  (* neighbors *)
  val neighbor_of : int -> mat -> int -> int list
  val commonneighbor_of : int -> mat -> int * int -> int list
  val inneighbor_of : int -> mat -> int -> int list
 
  (* properties *)
  val is_ackset : mat -> bool
  val not_automorphic : mat -> bool
  val number_of_edges : mat -> int
  val number_of_holes : mat -> int
  
  (* converting from matrix representation to list of edges *)
  val mat_to_edgecl : mat -> ((int * int) * int) list
  val edgecl_to_mat : ((int * int) * int) list -> mat
  val edgecl_to_mat_size : int -> ((int * int) * int) list -> mat
  
   
end
