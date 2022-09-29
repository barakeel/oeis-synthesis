signature hadamard =
sig

  val wilson_score : int vector * int vector * int vector * int vector -> int
  val wilson_score2 : int vector * int vector * int vector * int vector -> int
  
  exception Success of int list list
  val size_glob : int ref
  val explo : real ref
  
  type move = int list
  val movev : move vector
  
  datatype mtree = MNode of 
    move list * real ref * real ref  * mtree option ref vector 
  val init_tree : unit -> mtree
  val mcts : mtree -> int -> mtree
  
end
