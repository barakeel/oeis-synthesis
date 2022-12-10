signature search =
sig

  (* counting tree: move to a new file *)
  datatype ctree = 
    Cleaf of int list |
    Cvect of int * ctree option vector
  val ct_glob : ctree ref
  val ctempty : ctree
  val cadd : int list -> ctree -> ctree
  val cplayer : ctree -> game.board -> real * (int * real) list
  
  (* search *)
  val randsearch_flag : bool ref
  val search : (int * real) -> unit
  val search_board : (int * real) -> kernel.prog list -> unit
  
  (* beam search: move to a new file *)
  val beamsearch : unit -> (int * (int * kernel.prog) list) list
  
end
