signature ramsey =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  
  val exist_clique : int -> (int * int -> bool) -> int list -> bool
  val enum_shapel : int * int -> (int * int -> bool) -> int list * IntInf.int
  val double_graph : bool Array2.array -> int -> prog -> bool Array2.array option
  val ramsey_score : prog -> (int * IntInf.int) option
  
  
  
  
end
