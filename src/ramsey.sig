signature ramsey =
sig
  
  include Abbrev
  
  type prog = kernel.prog
    
  val loop_minclique : (int * int -> bool) -> int * int -> 
    (int * IntInf.int) * ((int * int) list * (int * int) list)
  val ramsey_score : prog -> (int * IntInf.int) option
  
end
