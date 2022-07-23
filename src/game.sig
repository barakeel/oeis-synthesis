signature game =
sig

  type move = int
  val maxmove : int
  
  type board = kernel.prog list

  (* recording programs during the search *)
  val record_flag : bool ref
  val progd: kernel.prog Redblackset.set ref
  val online_flag : bool ref
  exception ResultP of kernel.prog;
   
  (* parameters *)
  val noise_flag : bool ref 
  val noise_coeff_glob : real ref
  val nsim_opt : int option ref
  val time_opt : real option ref
  val mctsparam : unit -> mcts.mctsparam
   
  (* game *)
  val game : (board,move) mcts.game
  
  (* conversion between a sequence of moves and a board *)
  val linearize_board : board -> (board * move) list
  val linearize : kernel.prog -> (board * move) list
  val linearize_safe : kernel.prog -> (board * move) list
  val apply_movel : move list -> board -> board
  
  (* for test *)
  val random_prog : int -> kernel.prog
  val random_board : int -> board
  
end
