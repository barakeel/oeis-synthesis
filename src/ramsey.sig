signature ramsey =
sig

  type mat = int Array2.array
  val mat_sub : mat * int * int -> int 
  val mat_size : mat -> int

  val continue_flag : bool ref
  val degree_flag : bool ref

  (* sat *)            
  val all_clauses : int -> mat * mat -> (int * int) list list
  val extra_clauses : int -> (int * int) list list
  
  val init_sat : int -> mat * mat ->
     (int ref *
       (((int ref * int ref) * (int * int)) vector *
       ((int ref * int ref) * (int * int)) vector)) vector *
     ((bool ref * ((int * int) * int)) vector * int ref) vector
  
  val sat_solver : int -> mat * mat -> bool
  
  (* random shapes *)
  val random_mat : int -> mat
  val matK : int -> mat
  val matKn : int -> int -> mat
  val random_shape : int -> int -> mat
  val random_shape_nocycle : int -> int -> mat
  val symmetrify : mat -> mat
  val string_of_graph : mat -> string
  val string_of_bluegraph : mat -> string
  
  (* search tools *)
  val search_order : int -> (int * int) list
  val search_order_linear : int -> (int * int) list
  val edgel_glob : (int * int) list ref
  val subsets_of_size : int -> int list -> int list list
  
  (* normalization *)
  val refine_partition : int list list -> int list list list
  val normalize_nauty : mat -> mat
  val normalize_nauty_safe : mat -> mat
  
  (* properties *)
  val is_ackset : mat -> bool
  val is_ackset_pb : (mat * mat) -> bool
  val not_automorphic : mat -> bool
  val not_automorphic_pb : (mat * mat) -> bool
  val has_cycle : int -> mat -> bool
  
  (* rl experiment *)
  val ramsey_score : kernel.prog -> int option  

  
end
