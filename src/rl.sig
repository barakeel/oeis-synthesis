signature rl =
sig

  include Abbrev

  type seq = kernel.seq
  type prog = kernel.prog
  type sol = kernel.sol
  type tnn = mlTreeNeuralNetwork.tnn
  type 'a set = 'a Redblackset.set
  type ('a,'b) dict = ('a,'b) Redblackmap.dict
  type anum = bloom.anum
  
  (* globals *)
  val nvis : int ref
  val rtim : real ref
  val maxgen : int option ref
  val ngen_glob : int ref
  val expname : string ref

  (* functions *)
  val search : unit -> int -> sol list
  val parspec : (unit, int, sol list) smlParallel.extspec
  val trainf_start : unit -> unit
  val trainf_end : unit -> unit
  
  (* reinforcement learning *)
  val rl_search_only : int -> unit
  val rl_train_only : int -> unit
  val rl_search : int -> unit
  val rl_train : int -> unit
 
  (* continuous training and searching *)
  val rl_search_cont : unit -> unit
  val rl_train_cont : unit -> unit

  (* interactive search *)
  val search_target : IntInf.int list -> kernel.prog option
 
  (* cube and conquer *)
  val start_cube : int -> seq -> (prog list, int) mcts.tree * prog list
  val search_cube : unit -> (prog list * real) -> sol list
  val cubespec : (unit, (prog list * real), sol list) smlParallel.extspec
  val init_cube : unit -> unit
  val get_boardsc : (prog list, int) mcts.tree -> (prog list * real) list
  
end
