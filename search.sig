signature search =
sig

  type prog = kernel.prog
  type emb = real vector
  val i_alt : int ref
  val i_glob : int ref
  val threshold_glob : real ref 
  val tnn_glob : mlTreeNeuralNetwork.tnn ref
  val zip_prog : prog -> Arbint.int
  val unzip_prog : Arbint.int -> prog
  
  val search : unit -> Arbint.int list
  
end
