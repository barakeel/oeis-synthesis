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
  val nvis : int ref
  val maxgen : int option ref
  val ngen_glob : int ref
  val expname : string ref
  val use_random : bool ref
  
  (* functions *)
  val search : tnn -> int -> (anum * prog) list
  val trainf_start : unit -> unit
  val trainf_end : unit -> unit
  
  (* reinforcement learning *)
  val rl_search_only : int -> unit
  val rl_train_only : int -> unit
  val rl_search : int -> unit
  val rl_train : int -> unit
  val parspec : (tnn, int, (anum * prog) list) smlParallel.extspec

  (* continuous training and searching *)
  val rl_search_cont : unit -> unit
  val rl_train_cont : unit -> unit

  (* solutions I/O *)
  val read_isol : int -> (anum * prog) list
  val string_of_iprog : (anum * prog) -> string
  
  (* interactive search *)
  val search_target : mlTreeNeuralNetwork.tnn -> IntInf.int list -> 
    kernel.prog option
 
  
end