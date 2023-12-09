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

  (* functions *)
  val search : unit -> int -> sol list
  val parspec : (unit, int, sol list) smlParallel.extspec
  val trainf_start : int -> unit
  val trainf_end : int -> unit
  
  (* reinforcement learning wrappers *)
  val rl_search_only : int -> unit
  val rl_train_only : int -> unit
  val rl_search : int -> unit
  val rl_train : int -> unit
  val rl_search_cont : unit -> unit
  val rl_train_cont : unit -> unit
  val rl_search_cont_nowait : unit -> unit
  
  (* interactive search *)
  val search_target : IntInf.int list -> kernel.prog option
 
  (* cube and conquer *)
  val start_cube : int -> (prog list, int) mcts.tree
  val search_cube : unit -> (prog list * real) list -> sol list
  val cubespec : (unit, (prog list * real) list, sol list) smlParallel.extspec
  val init_cube : unit -> unit
  val get_boardsc : (prog list, int) mcts.tree -> (prog list * real) list
  
  (* pgen experiment *)
  val search_pgen : unit -> (prog list * real) list -> kernel.pgen list
  val pgenspec : 
    (unit, (prog list * real) list, kernel.pgen list) smlParallel.extspec
  
  (* searching for hadamard matrices *)
  val search_ramsey : unit -> (prog list * real) list -> kernel.ramsey list
  val ramseyspec : 
    (unit, (prog list * real) list, kernel.ramsey list) smlParallel.extspec
  
  (* standalone training function from a isol *)
  val trainf_isol : string -> (int * kernel.prog) list -> unit
  
  (* train one network for selecting data sets *)
  val train_smartselect : int -> unit
  
  
end
