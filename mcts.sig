signature mcts =
sig

  include Abbrev

  type seq = kernel.seq
  type prog = kernel.prog
  type progi = kernel.progi
  type clause = int * progi
  type tnn = mlTreeNeuralNetworkAlt.tnn
  type 'a set = 'a Redblackset.set
  
  datatype move = Unit of int | Oper of int * int | Pair
  datatype clausex = C1 of clause | C2 of clause * clause
  type board = clausex list  
  type player = (board,move) psMCTS.player

  (* globals *)
  val use_semb : bool ref
  val progd: progi Redblackset.set ref
  val notprogd: progi Redblackset.set ref
  val embd : (term, real vector) Redblackmap.dict ref
  val semd : seq Redblackset.set ref
  val seqwind : seq Redblackset.set ref
  val progwind : progi Redblackset.set ref

  (* game *)
  val game : (board,move) psMCTS.game
  
  (* players *)
  val player_uniform : tnn -> player
  val player_wtnn : tnn -> player
  val player_wtnn_cache : tnn -> player
  val player_glob : (tnn -> player) ref

  (* tracing solutions *)
  val stats_sol : string -> prog list -> unit
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
  val read_ctnn_fixed : unit -> tnn
  val dim_glob : int ref
  val get_tnndim : unit -> (term * int list) list

  (* functions *)
  val search : tnn -> int -> prog list
  val trainf : string -> unit

  (* reinforcement learning *)
  val expname : string ref
  val ngen_glob : int ref
  val rl_search_only : string -> int -> unit
  val rl_train_only : string -> int -> unit
  val rl_search : string -> int -> unit
  val rl_train : string -> int -> unit
  val parspec : (tnn,int,prog list) smlParallel.extspec

  (* standalone search function *)
  val search_target : real -> seq -> unit
 
  (* parallel search function *)
  val partargetspec : (real, seq, bool * string * real) smlParallel.extspec
  val parsearch_targetl : 
    int -> real -> seq list -> (bool * string * real) list  

  (* reading solutions *)
  val read_sold : int -> prog set
  val read_result : string -> prog list

end
