signature ramsey =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  val ramsey_score : prog -> int * IntInf.int
  
end
