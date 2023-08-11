signature ramsey =
sig

  type mat = int Array2.array
  val mat_sub : mat * int * int -> int 
  val mat_size : mat -> int

  val continue_flag : bool ref
  val degree_flag : bool ref
  val max_red_degree : int ref
  val max_blue_degree : int ref
  val iso_flag : bool ref
  val del_flag : bool ref
  val sbl_flag : bool ref
  val graphl : IntInf.int list ref
  val disable_log : bool ref
  
  (* sat *)            
  val all_clauses : int -> mat * mat -> (int * int) list list
  val sbl_clauses : int -> (int * int) list list
  
  val init_sat : int -> mat * mat ->
     (int ref *
       (((int ref * int ref) * (int * int)) vector *
       ((int ref * int ref) * (int * int)) vector)) vector *
     ((bool ref * ((int * int) * int)) vector * int ref) vector
  
  val sat_solver : int -> mat * mat -> bool
  
  (* storing full matrices *)
  val zip_full : mat -> IntInf.int
  val unzip_full : int -> IntInf.int -> mat
  val unzip_full_edgecl : int -> IntInf.int -> ((int * int) * int) list
  
  (* creating problems *)
  val all_clauses2 : int -> int * int -> ((int * int) * int) list list
  val all_clauses3 : int -> int * int -> int Array2.array
    -> ((int * int) * int) list list
  
  (* random shapes *)
  val random_mat : int -> mat
  val random_full_symmat : int -> mat
  val mat_compare : mat * mat -> order
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

  (* r45 experiment *)
  val init_subgraphs : unit -> unit
  val ramseyspec : (unit, int, bool) smlParallel.extspec
  val r45 : int -> string -> unit

  
end
