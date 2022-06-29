signature mizar =
sig

  include Abbrev

  type prog = kernel.prog
  type sexp = human.sexp

  val collect_tokens : sexp -> string list
  val rm_squote_sexp : sexp -> sexp
  val sexp_to_prog: (string, int) Redblackmap.dict -> sexp -> prog
  val collect_arity : prog list -> (int, int) Redblackmap.dict

  type board = kernel.prog list * kernel.prog list * int list 
  type move = int
  val random_board : int -> board
  val linearize_safe : prog list -> (board * move) list
 
  val term_of_board : board -> term
  val pbl1 : prog list list
  val create_exl : prog list list -> (term * real list) list list
  val export_traindata : (term * real list) list list -> unit
  (*
  val wind : prog Redblackset.set ref
  val mizard : prog Redblackset.set
  val init_wind : unit -> unit

  val game : (board,move) psMCTS.game
  val player_uniform :  tnn -> int list * prog list -> real * (int * real) list
  val mctsobj : tnn -> (board,move) mcts.mctsobj
  *)
  

end
