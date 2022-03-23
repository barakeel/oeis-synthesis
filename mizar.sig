signature mizar =
sig

  include Abbrev
  type tnn = mlTreeNeuralNetworkAlt.tnn
  type 'a set = 'a Redblackset.set

  datatype sexp = Sexp of sexp list | Stoken of string;
  val lex_sexp : string -> string list
  val parse_sexp : string -> sexp

  val rm_squote_sexp : sexp -> sexp
  val compress_arity : sexp -> sexp 
  val collect_tokens : sexp -> string list
 
  datatype prog = Ins of (int * prog list)
  val prog_compare : prog * prog -> order 
  val prog_size : prog -> int
  val prog_compare_size : prog * prog -> order

  val sexp_to_prog: (string, int) Redblackmap.dict -> sexp -> prog
  val collect_arity : prog list -> (int, int) Redblackmap.dict
  val arityd : (int, int) Redblackmap.dict

  type board = int list * prog list
  type move = int
  
  val nsim_opt : int option ref
  val time_opt : real option ref  

  (* *)
  val wind : prog Redblackset.set ref
  val mizard : prog Redblackset.set
  val init_wind : unit -> unit

  (* *)
  val game : (board,move) psMCTS.game
  val player_uniform :  tnn -> int list * prog list -> real * (int * real) list
  val mctsobj : tnn -> (board,move) psMCTS.mctsobj
  val tree_size : ('a, 'b) psMCTS.tree -> int

  

(*
  type move = int
*)
(*
  type seq = kernel.seq
  type prog = kernel.prog
  type progi = kernel.progi
  type clause = int * progi
  type tnn = mlTreeNeuralNetworkAlt.tnn
  type 'a set = 'a Redblackset.set
  
  datatype move = Oper of int * int | Pair
  datatype clausex = C1 of clause | C2 of clause * clause
  type board = clausex list  
  type player = (board,move) psMCTS.player

  val prog_compare_size : prog * prog -> order
  val compute_freq : (prog -> prog list) -> prog list -> (prog * int) list

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
  val use_cache : bool ref
  val use_ob : bool ref
  val uniform_flag : bool ref
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
  val search_target_aux : tnn * kernel.prog set -> real -> seq -> prog option
 
  (* parallel search function *)
  val partargetspec : (real, seq, bool * string * real) smlParallel.extspec
  val parsearch_targetl : 
    int -> real -> seq list -> (bool * string * real) list  

  (* reading solutions *)
  val read_sold : int -> prog set
*)

end
