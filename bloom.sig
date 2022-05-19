signature bloom =
sig

  type prog = kernel.prog
  type seq = kernel.seq
  
  (* OEIS array *)
  val oseq : Arbint.int list option array
  
  (* tree of OEIS sequences *)
  datatype ttree = 
    Tleaf of int * Arbint.int list |
    Tdict of int list * (Arbint.int, ttree) Redblackmap.dict
  val tempty : ttree
  val tadd : Arbint.int list * int -> ttree -> ttree
  val tcover : (Arbint.int * Arbint.int -> Arbint.int) -> int list
  val ost : ttree

  (* user-given sequence *)
  val fcover : (Arbint.int * Arbint.int -> Arbint.int) -> Arbint.int list -> 
    bool

end
