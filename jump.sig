signature jump =
sig

datatype jtree = 
  Jleaf of int list |
  Jdict of (bool * (int, jtree) Redblackmap.dict)

val jadd : int list -> jtree -> jtree

end
