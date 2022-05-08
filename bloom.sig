signature bloom =
sig

  type prog = kernel.prog
  type seq = kernel.seq
  
  (* OEIS array *)
  val oseq : Arbint.int list option array
  
  (* program quotient *)
  datatype stree = 
    Sleaf of prog * int list |
    Sdict of (int, stree) Redblackmap.dict

  exception Sexists
  val sempty : stree
  val sadd : prog * seq -> stree -> stree 
  val snew : prog * seq -> stree -> bool * prog option

  (* tree of OEIS sequences (todo change it to arbitrary precision) *)
  datatype ttree = 
    Tleaf of int * Arbint.int list |
    Tdict of int list * (Arbint.int, ttree) Redblackmap.dict
  val tempty : ttree
  val tadd : Arbint.int list * int -> ttree -> ttree
  val tcover : (Arbint.int * Arbint.int -> Arbint.int) -> int list
  val ost : ttree

end
