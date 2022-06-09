signature bloom =
sig

  type prog = kernel.prog
  type seq = kernel.seq
  type anum = int
  
  (* OEIS array *)
  val oseq : Arbint.int list option array
  val oseql : (int * Arbint.int list) list

  (* tree of OEIS sequences *)
  datatype otree = 
    Oleaf of anum * Arbint.int list |
    Odict of anum list * (Arbint.int, otree) Redblackmap.dict
  val oempty : otree
  val oadd : Arbint.int list * int -> otree -> otree
  val cover_oeis : (Arbint.int * Arbint.int -> Arbint.int) -> 
                   (anum list * (int * real option) * anum list)
  val otree : otree

  (* user-given sequence *)
  val cover_target : (Arbint.int * Arbint.int -> Arbint.int) -> 
    seq -> bool * int

end
