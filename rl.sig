signature rl =
sig

  include Abbrev

  type seq = kernel.seq
  type prog = kernel.prog
  type tnn = mlTreeNeuralNetwork.tnn
  type 'a set = 'a Redblackset.set
  type ('a,'b) dict = ('a,'b) Redblackmap.dict

  type move = int
  type board = prog list
  type player = (board,move) mcts.player

  (* globals *)
  val ncore : int ref
  val ntarget : int ref
  val maxgen : int option ref
  val in_search : bool ref

  (* data *)
  val progd: prog set ref
  val embd : (term, real vector) dict ref
  val wind : (int, prog) dict ref

  (* game *)
  val game : (board,move) mcts.game
    
  (* players *)
  val player_uniform : tnn -> player
  val player_wtnn : tnn -> player
  val player_wtnn_cache : tnn -> player
  val player_glob : (tnn -> player) ref

  (* replaying solutions *)
  val linearize : prog -> (board * move) list
  val apply_movel : move list -> board -> board 
  val random_board : int -> board
  val random_prog : int -> prog
  
  (* search parameters *)
  val wnoise_flag : bool ref
  val noise_coeff_glob : real ref
  val noise_flag : bool ref
  val nsim_opt : int option ref
  val time_opt : real option ref  
  val coreid_glob : int ref

  (* train parameters *)
  val use_mkl : bool ref
  val dim_glob : int ref
  val get_tnndim : unit -> (term * int list) list

  (* functions *)
  val search : tnn -> int -> (int * prog) list
  val trainf : string -> unit

  (* reinforcement learning *)
  val expname : string ref
  val ngen_glob : int ref
  val rl_search_only : string -> int -> unit
  val rl_train_only : string -> int -> unit
  val rl_search : string -> int -> unit
  val rl_train : string -> int -> unit
  val parspec : (tnn, int, (int * prog) list) smlParallel.extspec

  (* reading solutions *)
  val read_isol : int -> (int * prog) list

  (* interactive search *)
  val search_target : mlTreeNeuralNetwork.tnn -> Arbint.int list -> 
    kernel.prog option
 
end
