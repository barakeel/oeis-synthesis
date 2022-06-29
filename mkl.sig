signature mkl =
sig

  include Abbrev
  type tnn = mlTreeNeuralNetwork.tnn

  val export_traindata : int * int * 
    (term, int) Redblackmap.dict * term list ->
    (term * real list) list list -> unit
  val read_ctnn : term list -> string list -> tnn


end
