signature gen =
sig

  type mat = int Array2.array
   
  val fgen_flag : bool ref 
   
  (* generalization tree *)
  val all_children : mat -> mat list
  val all_parents : mat -> mat list
  val all_leafs : mat -> mat list

  (* generalization *)
  val rgeneralize_one : int * int -> mat list -> mat list
  val fgeneralize : mat Redblackset.set -> mat -> mat list list
  val ggeneralize : mat list -> (mat * mat list) list

  (* cover *)
  val gen_width : int ref
  val gen_depth : int ref
  val compute_cover : mat list -> (mat * mat list) list
  val compute_scover : (int * int) -> mat list -> mat list
  
  (* cones *)
  val ccover : int list list -> int list list
  
  (* parallelization *)
  (*
  val coverspec : (mat list, mat, mat list) smlParallel.extspec
  val loop_cover_para :  string -> int -> mat list -> (mat * mat list) list
  *)
  
  
  
end
