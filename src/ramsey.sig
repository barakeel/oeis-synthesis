signature ramsey =
sig
  
  include Abbrev
  
  type prog = kernel.prog
    
  val loop_minclique : (int * int -> bool) -> int * int -> 
    (int * IntInf.int) * ((int * int) list * (int * int) list)
  val ramsey_score : prog -> (int * IntInf.int) option
  
  val derive : int list -> int list
  
  val execspec : (unit, prog, int * (int list * int list)) smlParallel.extspec
  val no_hash : bool ref
  val parallel_exec : string -> unit
  val skip_test : bool ref
  
  (* approximate maximum clique finder *)
  val bestfirst_clique : int -> 
    (int * int -> bool) -> int list -> int list -> int list
  
end
