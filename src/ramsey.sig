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
  val generalize : mat list -> mat -> mat list list
  val find_best_mpll : mat Redblackset.set -> mat list list -> mat * (int * int)
  val compute_cover : mat list -> (mat * mat list) list
  
  (* r45 experiment *)
  val init_subgraphs : unit -> unit
  val satdir_glob : string ref
  val ramseyspec : (unit, int, bool) smlParallel.extspec
  val r45 : int -> string -> unit
  (* val create_cone : mat * mat -> int -> string -> bool *)
  (* r45 alternative *)
 
  val evalspec : 
    ((int * int * int), (IntInf.int * IntInf.int) list, bool list)
    smlParallel.extspec
  val eval_loop35 : string -> int * int -> int -> unit
  val eval_loop44 : string -> int -> int * int -> unit
  
end
