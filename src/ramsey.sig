signature ramsey =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  val ramsey_score : prog -> int * IntInf.int
  
  val enum_shapel_free : 
    int -> (int * int -> bool) -> (int * int) list * IntInf.int
  
end
