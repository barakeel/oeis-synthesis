signature rl =
sig

  include Abbrev

  type seq = kernel.seq
  type prog = kernel.prog
  type tnn = mlTreeNeuralNetwork.tnn
  type 'a set = 'a Redblackset.set
  type ('a,'b) dict = ('a,'b) Redblackmap.dict

  datatype move = O of int * bool | P of bool | Q
  type board = prog list list
  type player = (board,move) mcts.player

  val compute_freq : (prog -> prog list) -> prog list -> (prog * int) list

  (* globals *)
  val ncore : int ref
  val ntarget : int ref
  val maxgen : int option ref
  val in_search : bool ref

  (* data *)
  val progd: prog set ref
  val notprogd: prog set ref
  val embd : (term, real vector) dict ref
  val wind : (int, prog) dict ref

  (* game *)
  val game : (board,move) mcts.game
  
  (* ordering constraints reordering arguments *)
  val weak_ord : board -> bool
  val strong_ord : board -> bool

  (* players *)
  val player_uniform : tnn -> player
  val player_wtnn : tnn -> player
  val player_wtnn_cache : tnn -> player
  val player_glob : (tnn -> player) ref

  (* tracing solutions *)
 (* val stats_sol : string -> prog list -> unit *)
  val linearize : prog -> (board * move) list
  val apply_movel : move list -> board -> board 
  val random_board : int -> board
  val random_prog : int -> prog
  
  (* search parameters *)
  val use_ob : bool ref
  val wnoise_flag : bool ref
  val noise_coeff_glob : real ref
  val noise_flag : bool ref
  val nsim_opt : int option ref
  val time_opt : real option ref  
  val coreid_glob : int ref

  (* train parameters *)
  val use_mkl : bool ref
  val use_para : bool ref
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

end
