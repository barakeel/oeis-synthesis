signature bloom =
sig

  type prog = kernel.prog
  type seq = kernel.seq
  type anum = int
  
  (* OEIS array *)
  val oseq : seq option array
  val oseql : (int * seq) list
  val select_random_target : unit -> unit
  val select_random_target_avoiding : int Redblackset.set -> unit
  val select_random_target2 : unit -> (int * seq)

  (* tree of OEIS sequences *)
  datatype otree = 
    Oleaf of anum * IntInf.int list |
    Odict of anum list * (IntInf.int, otree) Redblackmap.dict
  val oempty : otree
  val oadd : IntInf.int list * int -> otree -> otree
  val otree : otree
  val cover_oeis : (IntInf.int -> IntInf.int) -> 
                   ((anum * int) list * int * anum list)
  val scover_oeis : (IntInf.int -> IntInf.int) -> (anum * int) list


  (* user-given sequence *)
  val cover_target : (IntInf.int -> IntInf.int) -> 
    seq -> bool * int

  (* FS data *)
  val fsmap : (string * int vector) list
  val perml : int list list
  val permd : (int list, int) Redblackmap.dict
  val permv : int list vector
  val perminputv : int list vector
  val apply_mapl : string list -> int list -> int list
  val mapl : string list
  val compv : string list vector
  
  (* debug *)
  datatype otreen = 
    Oleafn of anum * IntInf.int list |
    Odictn of anum list * (IntInf.int * otreen) list

  val rm_dict : otree -> otreen

end
