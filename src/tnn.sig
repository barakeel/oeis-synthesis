signature tnn =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  type player = (game.board,game.move) mcts.player

  (* globals *)
  val embd : (term, real vector) Redblackmap.dict ref
  val operlext : term list
  val get_tnndim : unit -> (term * int list) list
  val tnn_glob : tnn ref (* for debugging *)

  (* for search *) 
  val stack_cat : term
  val stack_empty : term
  val pair_progseq : term
  val prepoli : term
  val head_poli : term
  val cap_tm : term -> term
  val fp_emb_either : term -> real vector list -> real vector
  val get_targete : unit -> real vector
  val infer_emb_nocache : term -> real vector
  val term_of_prog : kernel.prog -> term
  val term_of_stack : kernel.prog list -> term
   
  (* tnn-based players (should be moved to game) *)  
  val player_uniform : player
  val player_random : player
  val player_wtnn_cache : player
  val player_glob : player ref

  (* training I/O *)
  val create_exl : (int * kernel.prog) list -> (term * real list) list list
  val create_exl_seqprogl : 
    (kernel.seq * kernel.prog) list -> (term * real list) list list
  
  val create_exl_progset : kernel.prog list -> (term * real list) list list
  
  
  val export_traindata : string -> int -> real -> 
    (term * real list) list list -> unit
  
  (* deprecated *)
  val read_ctnn : string list -> tnn
  
  (* inference *)
  val fp_op_glob : (term -> real vector list -> real vector) ref
  val update_fp_op : string -> unit  
  
end
