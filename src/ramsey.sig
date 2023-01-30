signature ramsey =
sig

  val cut : bool Array2.array -> int -> bool Array2.array
  val mk_sym : bool Array2.array -> int -> bool Array2.array
  val invert : bool Array2.array -> int -> bool Array2.array
  val all_clique :  bool Array2.array -> 
    int -> int -> (int list * int) list -> (int list * int) list

  val edge_proba : real ref
  val ramsey : 
    (int * int -> bool) -> int -> int -> int -> bool Array2.array * int
  val all_charac : bool Array2.array -> int -> (int * int list) list
  val norm_graph : bool Array2.array -> int -> bool Array2.array
  
  
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
  
end
