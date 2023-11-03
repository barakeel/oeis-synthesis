signature cone =
sig

  val attempts_glob : int ref

  val write_cone : 
    int * int -> IntInf.int -> (int list * int list list) list -> unit
  val read_cone : 
    int * int -> IntInf.int -> (int list * int list list) list
  val gen_cone : int * int -> IntInf.int -> unit
  
  val conespec : (int * int, IntInf.int, unit) 
    smlParallel.extspec 
  
  val cones45 : int -> int -> int * int -> unit
  
end
