signature jump =
sig

  datatype jtree = 
    Jleaf of game.move list |
    Jdict of (bool * (game.move, jtree) Redblackmap.dict)

  val best_subprog : kernel.prog Redblackset.set -> 
    kernel.prog list -> kernel.prog option
  val create_jtree_board : game.board list -> jtree
  val create_jtree : kernel.prog list -> jtree
  val jump : jtree -> game.board -> game.move list option
  val shortcut : jtree -> kernel.prog -> (game.board * game.move) list
  
end
