signature glue =
sig
  
  include Abbrev
  type mat = int Array2.array

  val both_flag : bool ref (* does not seem to give any benefit *)

  val glue_pb : bool -> int * int -> IntInf.int -> IntInf.int -> term
  val glue : bool -> (int * int) -> IntInf.int -> IntInf.int -> thm
  val write_gluescripts : string -> int -> bool -> 
    (int * int * int) -> (int * int * int) -> (int * int) -> unit


end
