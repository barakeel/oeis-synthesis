signature execarb =
sig

  type prog = kernel.prog
  
  val compr_cache : ((Arbint.int * Arbint.int -> Arbint.int) *
    (Arbint.int, Arbint.int) Redblackmap.dict ref) list ref

  val compr_f_aux : (Arbint.int * Arbint.int -> Arbint.int) * Arbint.int -> 
    Arbint.int
  val mk_execarb : prog -> Arbint.int * Arbint.int -> Arbint.int
  val find_wins : prog -> int list

end
