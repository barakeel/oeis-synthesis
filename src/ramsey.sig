signature ramsey =
sig

  type mat = bool vector vector
  type graph = mat * mat * int
  datatype branch = Follow | Avoid | Backtrack
  val edgel : (int * int) list
  val edgev : (int * int) vector
  val starting_graph : graph
  val ramsey : (int * int -> bool) -> graph
  
  val mat_to_list : mat * int -> bool list
  val mat_sub : mat * int * int -> bool
  val norm_graph : graph -> mat * int
 (* 
  type board = bool vector vector * bool vector vector * int
  val mall_clique :  bool vector vector -> 
    int -> (int list * int) list -> (int list * int) list
  val starting_board : board
  val apply_move : board -> bool -> board option
  val simul : int -> board -> real
  
  val bestscore : real ref
  val nsimul : int ref
  
  type move = bool
  datatype mtree = MNode of board * real ref * real ref  * mtree option ref vector 
  val init_tree : unit -> mtree
  val mcts : mtree -> int -> mtree
  
  val bigsteps : int -> mtree -> unit
  
  val ramseyspec : (unit, unit, unit) smlParallel.extspec
  val bigsteps_parallel : string -> int -> unit list
  *)
  
end
