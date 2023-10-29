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
  val compute_scover : (int * int) -> mat list -> 
    (IntInf.int * (IntInf.int * int list) list) list
  
  (* cones *)
  val ccover : int list list -> int list list
  
  (* parallelization *)
  val genspec : ((int * int) * IntInf.int Redblackset.set, IntInf.int, 
    IntInf.int * (IntInf.int * int list) list) smlParallel.extspec
  val compute_scover_para : int -> int * int ->
    IntInf.int Redblackset.set -> 
    (IntInf.int * (IntInf.int * int list) list) list
  
  
  
end
