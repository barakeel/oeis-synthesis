signature gen =
sig

  type mat = int Array2.array
   
  (* generalization tree *)
  val all_parents : mat -> mat list
  val all_leafs : mat -> mat list
  val all_children : mat -> mat list
  val all_descendants : int -> mat -> mat list

  (* generalization *)

  (* cover *)
  val gen_width : int ref
  val compute_hcover : mat list -> (mat * mat list) list
  val compute_cover : mat list -> (mat * mat list) list
  
  
  (*
  val coverspec : (mat list, mat, mat list) smlParallel.extspec
  val loop_cover_para :  string -> int -> mat list -> (mat * mat list) list
  *)
  
end
