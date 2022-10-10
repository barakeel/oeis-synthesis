signature bloom =
sig

  type prog = kernel.prog
  type seq = kernel.seq
  type anum = int
  
  (* OEIS array *)
  val oseq : IntInf.int list option array
  val oseql : (int * IntInf.int list) list
  val select_random_target : unit -> unit

  (* tree of OEIS sequences *)
  datatype otree = 
    Oleaf of anum * IntInf.int list |
    Odict of anum list * (IntInf.int, otree) Redblackmap.dict
  val oempty : otree
  val oadd : IntInf.int list * int -> otree -> otree
  val cover_oeis : (IntInf.int -> IntInf.int) -> 
                   ((anum * int) list * int * anum list)
  val otree : otree

  (* user-given sequence *)
  val cover_target : (IntInf.int -> IntInf.int) -> 
    seq -> bool * int


end
