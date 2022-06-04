signature rl =
sig

  include Abbrev

  type seq = kernel.seq
  type prog = kernel.prog
  type tnn = mlTreeNeuralNetwork.tnn
  type 'a set = 'a Redblackset.set
  type ('a,'b) dict = ('a,'b) Redblackmap.dict
  type anum = bloom.anum
 
  (* globals *)
  val ncore : int ref
  val coreid_glob : int ref
  val ntarget : int ref
  val maxgen : int option ref
  val ngen_glob : int ref
  val expname : string ref
  
  (* functions *)
  val search : tnn -> int -> (anum * prog) list * (anum * prog) list
  val trainf : string -> unit
  
  (* reinforcement learning *)
  val rl_search_only : string -> int -> unit
  val rl_train_only : string -> int -> unit
  val rl_search : string -> int -> unit
  val rl_train : string -> int -> unit
  val parspec : (tnn, int, (anum * prog) list * (anum * prog) list) 
    smlParallel.extspec

  (* solutions I/O *)
  val read_isol : int -> (anum * prog) list
  val string_of_iprog : (anum * prog) -> string
  
  (* interactive search *)
  val search_target : mlTreeNeuralNetwork.tnn -> Arbint.int list -> 
    kernel.prog option
 
  
end
