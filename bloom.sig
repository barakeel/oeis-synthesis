signature bloom =
sig

  type prog = kernel.prog
  type seq = kernel.seq
  val import_oseq :  unit -> (seq * string) list
  val import_arbseq :  unit -> (Arbint.int list * string) list
  
  (* quotient *)
  datatype stree = 
    Sleaf of int list |
    Sdict of (int, stree) Redblackmap.dict
  val sempty : stree
  val sadd : seq -> stree -> stree 
  val smem : seq -> stree -> bool * bool

  (* tree of OEIS sequences *)
  datatype ttree = 
    Tleaf of string * seq |
    Tdict of string list * string list * (int, ttree) Redblackmap.dict
  val tempty : ttree
  val tadd : seq * string -> ttree -> ttree
  val tcover : seq -> ttree -> string list
  val find_wins : seq -> string list
  val oseq : (int list * string) list
  val ost : ttree

end
