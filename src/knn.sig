signature knn =
sig

  val fea_of_prog : kernel.prog -> int list
  val knn : (int, real) Redblackmap.dict * (kernel.prog * int list) list ->
    int -> kernel.prog -> kernel.prog list
  val knn_gpt : string -> int -> unit
  
  (* parallel execution (wip) *)
  val knnspec : (int * string, string list, string list) smlParallel.extspec
  val parallel_knn_gpt : int -> string -> int -> unit
  
end