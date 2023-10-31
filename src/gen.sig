signature gen =
sig

  type mat = int Array2.array
  type vleafs = int * (IntInf.int * int list) list  
  
  (* generalization tree *)
  val all_children : mat -> mat list
  val all_parents : mat -> mat list
  val all_leafs : mat -> mat list
  
  (* parallelization *)
  val genspec : ((int * int) * IntInf.int Redblackset.set, IntInf.int, 
    IntInf.int * vleafs list) smlParallel.extspec
  val compute_scover_para : int -> int * int -> IntInf.int Redblackset.set -> 
    (IntInf.int * (IntInf.int * int list) list) list
  val store_cover :  int -> int * int ->
    (IntInf.int * (IntInf.int * int list) list) list -> unit
  val all_cover : int -> int * int -> int * int -> unit
  
  (* cones *)
  val ccover : int list list -> int list list
  
end
