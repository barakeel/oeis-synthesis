signature jump =
sig

type move = int

datatype jtree = 
  Jleaf of move list |
  Jdict of (bool * (move, jtree) Redblackmap.dict)

val count_subboard : kernel.prog list -> (game.board * int) list
val create_jtree : kernel.prog list -> jtree
val jump : jtree -> game.board -> game.board option

end
