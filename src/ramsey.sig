signature ramsey =
sig

  type mat = int Array2.array
 
  (* precompute 3,5 and 4,4 graphs *) 
  val read35 : int -> IntInf.int list
  val read44 : int -> IntInf.int list
  val read35gen : int -> IntInf.int list
  val read44gen : int -> IntInf.int list
  
  (* I/O tools *)  
  val convert : string -> string -> unit
  val read_stats : string -> ((mat * mat) * real) list
  
  (* r45 *)
  val ramseyspec : (unit, IntInf.int * IntInf.int, bool) smlParallel.extspec
  val r45 : int -> string -> int -> unit

  val glue : string -> IntInf.int * IntInf.int -> bool
  val glue_filein : string -> IntInf.int * IntInf.int -> string
  
end
