signature execarb =
sig

  type prog = kernel.prog
  val mk_execarb : prog -> Arbint.int * Arbint.int -> Arbint.int
  val find_wins : prog -> int list
  val pcover : prog -> Arbint.int list -> bool
  val penum : prog -> int -> Arbint.int list

end
