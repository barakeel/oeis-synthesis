signature ramsey =
sig
  
  include Abbrev
  
  type prog = kernel.prog
    
  val loop_minclique : (int * int -> bool) ->
    int * int -> (int * int) list * (int * int) list

end
