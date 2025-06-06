signature mkl =
sig

  include Abbrev
  type tnn = mlTreeNeuralNetwork.tnn

  val export_traindata : string -> int * int * 
    (term, int) Redblackmap.dict * term list * int * real ->
    (term * real list) list list -> unit
  val read_ctnn : term list -> string list -> tnn


end
