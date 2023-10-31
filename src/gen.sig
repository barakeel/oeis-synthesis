signature gen =
sig

  type mat = int Array2.array
  
  (* generalization tree *)
  val all_children : mat -> mat list
  val all_parents : mat -> mat list
  val all_leafs : mat -> mat list
  
  (* cover *)
  val compute_scover : (int * int) -> mat list -> 
    (IntInf.int * (IntInf.int * int list) list) list
  
  (* cones *)
  val ccover : int list list -> int list list
  
  (* parallelization *)
  val genspec : ((int * int) * IntInf.int Redblackset.set, IntInf.int, 
    IntInf.int * (IntInf.int * int list) list) smlParallel.extspec
  val compute_scover_para : int -> int * int -> IntInf.int Redblackset.set -> 
    (IntInf.int * (IntInf.int * int list) list) list
  val store_cover :  int -> int * int ->
    (IntInf.int * (IntInf.int * int list) list) list -> unit
  val all_cover : int -> int * int -> int * int -> unit
  
end
