signature rnn =
sig

  (* tokenization *)
  val tokseq : int
  val tokenize_seq : IntInf.int list -> int list
  val tokprog : int
  val tokenize_stack : game.board -> int list
  val tokhead : int 

  (* training using MKL *)
  val export_traindata : string -> int -> kernel.sol list -> unit

  (* inference using OpenBLAS *)
  val fp_op_glob : (int -> real vector list -> real vector) ref
  val update_fp_op : string -> unit  
  val fp_tok : int -> real vector list -> real vector (* input is reversed *)
  val fp_tokl : int list -> real vector list (* output is reversed *)
  

end
