signature search =
sig

  type prog = kernel.prog
  type emb = real vector

  val tnn_glob : mlTreeNeuralNetwork.tnn ref
  val search : int -> unit
  
end
