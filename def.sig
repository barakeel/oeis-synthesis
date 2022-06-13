signature def =
sig

  type prog = kernel.prog
  val arityd : (int, int) Redblackmap.dict ref
  val compression : prog list -> prog -> int
  val nbest_def :  
    int -> prog list -> (prog * int) list * kernel.prog list
  
  datatype atree = ANode of (prog * (prog list * int) list * 
    (int,atree) Redblackmap.dict list)
  val create_atree : int -> prog list -> atree
  val collect_def : atree -> (prog * int) list
  val nb_def : int ->
    int -> kernel.prog list -> (prog * int) list * prog list
    
end
