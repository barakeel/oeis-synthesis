signature search =
sig
  
  (* search *)
  val randsearch_flag : bool ref
  val search : (int * real) -> unit
  val search_board : (int * real) -> kernel.prog list -> unit
  
  (* beam search: move to a new file *)
  val beamsearch : unit -> (int * (int * kernel.prog) list) list
  val beamsearch_ordered : int -> kernel.seq -> 
    (kernel.seq * (kernel.prog * real)) list
  val beamsearch_target : int -> kernel.seq -> (kernel.prog * real) list
  
  (* self-selected training set *)
  val search_smartselect : string -> (int * (int * kernel.prog) list) list

end
