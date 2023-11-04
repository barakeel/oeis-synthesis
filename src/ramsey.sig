signature ramsey =
sig

  type mat = int Array2.array

  (* I/O tools *)  
  val convert : string -> string -> unit
  val read_stats : string -> ((mat * mat) * real) list
  
  (* r45 *)
  val ramseyspec : (unit, IntInf.int * IntInf.int, bool) smlParallel.extspec
  val r45 : int -> string -> int -> unit

  val glue : string -> IntInf.int * IntInf.int -> bool
  val glue_filein : string -> IntInf.int * IntInf.int -> string
  
end
