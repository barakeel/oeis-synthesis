signature gen =
sig

  type mat = int Array2.array
  type vleafs = int * int * (IntInf.int * int list) list  
  
  (* parameters *)
  val select_number1 : int ref
  val select_number2 : int ref
  
  
  
  
  (* parallelization *)
  val genspec : ((int * int) * IntInf.int Redblackset.set, IntInf.int, 
    IntInf.int * vleafs list) smlParallel.extspec
  val compute_scover_para : int -> int -> int * int -> 
    (IntInf.int * (IntInf.int * int list) list) list
  
  (* I/O *)
  val write_cover :  int -> int * int ->
    (IntInf.int * (IntInf.int * int list) list) list -> unit
  val read_cover : int -> int * int -> 
    (IntInf.int * (IntInf.int * int list) list) list
  val read_par : int -> int * int -> IntInf.int list
  
  (* main *)
  val gen : int -> int * int -> int * int -> unit
  
  (* cones *)
  val ccover : int list list -> int list list
  

end
