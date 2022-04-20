signature bloom =
sig

  type prog = kernel.prog
  type seq = kernel.seq
  val import_oseq :  unit -> (seq * string) list
  val import_arbseq :  unit ->
    (Arbint.int list * string) list * 
    (Arbint.int list, string list) Redblackmap.dict
  val import_arbseq_fst :  unit ->
    (Arbint.int list * string) list

  val odname_glob : (seq, string list) Redblackmap.dict ref
  val odv_glob : (seq Redblackset.set) vector ref
  val find_wins : prog -> seq -> seq list
  val init_od : unit -> unit

  datatype stree = 
    Sleaf of int list |
    Sdict of (int, stree) Redblackmap.dict

  val sempty : stree
  val sadd : seq -> stree -> stree 
  val smem : seq -> stree -> bool * bool

  datatype ttree = 
    Tleaf of string * seq |
    Tdict of string list * string list * (int, ttree) Redblackmap.dict
  
  val tempty : ttree
  val tadd : seq * string -> ttree -> ttree
  val tcover : seq -> ttree -> string list

end
