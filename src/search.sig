signature search =
sig
  
  (* search *)
  val randsearch_flag : bool ref
  val search : (int * real) -> unit
  val search_board : (int * real) -> kernel.prog list -> unit
  
  (* beam search: move to a new file *)
  val beamsearch : unit -> (int * (int * kernel.prog) list) list
  
end
