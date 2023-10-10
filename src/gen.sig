signature gen =
sig

  type mat = int Array2.array
   
  (* generalization tree *)
  val all_parents : mat -> mat list
  val all_leafs : mat -> mat list

  (* generalization *)
  val ggeneralize : mat list -> (mat * mat list) list

  (* minimization *)
  val minimize_cover : mat list -> (mat * mat list) list -> mat list

  (* search *)
  val cover_glob : (mat list * int) list ref
  val next_cover : int -> mat list * int -> (mat list * int) list

  (* cover *)
  val gen_width : int ref
  val gen_depth : int ref
  val compute_cover : mat list -> (mat * mat list) list
  
  (* parallelization *)
  (*
  val coverspec : (mat list, mat, mat list) smlParallel.extspec
  val loop_cover_para :  string -> int -> mat list -> (mat * mat list) list
  *)
  
  
  
end
