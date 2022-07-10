signature search =
sig

  type prog = kernel.prog
  type emb = real vector
  val i_glob : int ref
  val threshold_glob : real ref 
  val search : (prog * emb * emb) list * real -> unit
  val tnn_glob : mlTreeNeuralNetwork.tnn ref
  
end
