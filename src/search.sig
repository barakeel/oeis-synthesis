signature search =
sig
  
  type prog = kernel.prog
  type seq = kernel.seq
  (* search *)
  val randsearch_flag : bool ref
  val search : (int * real) -> unit
  val search_board : (int * real) -> prog list -> unit
  
  (* beam search: move to a new file *)
  val beamsearch : unit -> (int * (int * prog) list) list
  val beamsearch_ordered : int -> seq -> (seq * (prog * real)) list
  val beamsearch_target : int -> seq -> (prog * real) list
  
  (* self-selected training set *)
  val search_smartselect : string -> (int * (int * prog) list) list

  (* programs generating programs *)
  val random_pgenl : int -> real -> prog list
  val infer_pgenl : string -> int -> real -> prog list
  val random_roundl : int -> int -> int list list
  val round_one : int list -> 
    (prog * (int * bool) list) list -> (prog * (int * bool) list) list

  val genprogspec : (int list, prog list, 
    (prog * (int * int list) list) list * prog list) smlParallel.extspec

  val competition_pl : string * int -> int -> prog list -> prog list
  
  (* random generation: generators producing programs not generated before *)
  val filter_unique_prog : prog list -> prog list
  val filteruniquespec : 
    (unit, unit, (prog * prog list) list) smlParallel.extspec
  val parallel_filterunique : int -> prog list
  
end

