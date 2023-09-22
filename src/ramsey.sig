signature ramsey =
sig

  type mat = int Array2.array
 
  (* precompute 3,5 and 4,4 graphs *) 
  val read35 : int -> IntInf.int list
  val read44 : int -> IntInf.int list
  
  (* generalization *)
  val all_parents : mat -> mat list
  val all_leafs : mat -> mat list
  val all_children : mat -> mat list
  val generalize : mat Redblackset.set -> mat -> mat list list
  val find_best_mpll : mat Redblackset.set -> mat list list -> mat * (int * int)
  val compute_cover : mat list -> (mat * mat list) list
  
  (*
  val coverspec : (mat list, mat, mat list) smlParallel.extspec
  val loop_cover_para :  string -> int -> mat list -> (mat * mat list) list
  *)  
  
  (* r45 *)
  val ramseyspec : (unit, IntInf.int * IntInf.int, bool) smlParallel.extspec
  val r45 : int -> string -> int -> int -> unit

end
