signature search =
sig

  val randsearch_flag : bool ref
  val search : (int * real) -> unit
  val search_board : (int * real) -> kernel.prog list -> unit
  val beamsearch : unit -> (int * (int * kernel.prog) list) list
  
end
