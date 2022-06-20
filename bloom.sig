signature bloom =
sig

  type prog = kernel.prog
  type seq = kernel.seq
  type anum = int
  
  (* OEIS sequences in a list, array and tree format *)
  val oseq : Arbint.int list option array
  val oseql : (int * Arbint.int list) list
  datatype otree = 
    Oleaf of anum * Arbint.int list |
    Odict of anum list * (Arbint.int, otree) Redblackmap.dict
  val otree : otree

end
