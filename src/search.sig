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
  val random_pgenl : int -> real -> prog list
  val infer_pgenl : string -> int -> real -> prog list
  val mimicspec : (prog vector * (int * prog) list, (int * int) list, 
    ((int * int)  * (real * real)) list) smlParallel.extspec
  val compete_pgenl : string * int -> int -> prog list -> prog list
  val random_roundl : int -> real -> int list list
  
end

