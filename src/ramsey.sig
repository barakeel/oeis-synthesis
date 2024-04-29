signature ramsey =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  
  
  val enum_shapel : int * int -> (int * int -> bool) -> int list * IntInf.int
  val ramsey_score : prog -> (int * IntInf.int) option
  
  
  
end
