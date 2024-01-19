signature search =
sig
  
  type prog = kernel.prog
  type seq = kernel.seq
 
  (* search *)
  val randsearch_flag : bool ref
  val search : (int * real) -> unit
  val search_board : (int * real) -> prog list -> unit
  val beamsearch : unit -> (int * (int * prog) list) list
  
  (* pgen *)
  val random_batchl : int -> 'a list -> 'a list list
  val random_pgenl : int -> real -> prog list  
  val infer_pgenl : string -> int -> real -> prog list
  val mimicspec : ((int * prog) list, prog list, real list) smlParallel.extspec
  val compete_pgenl : string * int -> (int * prog) list -> prog list -> prog list

  
end

