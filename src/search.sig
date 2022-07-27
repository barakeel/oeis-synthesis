signature search =
sig

  val tnn_glob : mlTreeNeuralNetwork.tnn ref
  val randsearch_flag : bool ref
  val search : int -> unit
  
end
