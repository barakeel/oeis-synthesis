signature tnn =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  type player = (game.board,game.move) mcts.player

  (* globals *)
  val use_mkl : bool ref
  val dim_glob : int ref 
  val embd : (term, real vector) Redblackmap.dict ref
  val operlext : term list
  val get_tnndim : unit -> (term * int list) list

  (* tnn-based players *)  
  val player_uniform : tnn -> player
  val player_wtnn : tnn -> player
  val player_wtnn_cache : tnn -> player
  val player_glob : (tnn -> player) ref

  (* training I/O *)
  val create_exl : (int * kernel.prog) list -> (term * real list) list list
  val export_traindata : (term * real list) list list -> unit
  val read_ctnn : string list -> tnn

end