signature gen =
sig

  type mat = int Array2.array
  type vleafs = int * (IntInf.int * int list) list  
  
  (* generalization tree *)
  val all_children : mat -> mat list
  val all_parents : mat -> mat list
  val all_leafs : mat -> mat list
  
  (* parameters *)
  val select_number1 : int ref
  val select_number2 : int ref
  
  (* parallelization *)
  val genspec : ((int * int) * IntInf.int Redblackset.set, IntInf.int, 
    IntInf.int * vleafs list) smlParallel.extspec
  val compute_scover_para : int -> int -> int * int -> 
    (IntInf.int * (IntInf.int * int list) list) list
  val store_cover :  int -> int * int ->
    (IntInf.int * (IntInf.int * int list) list) list -> unit
  val gen : int -> int * int -> int * int -> unit
  
  (* cones *)
  val ccover : int list list -> int list list
  

end
