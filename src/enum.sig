signature enum =
sig
  
  include Abbrev
  type mat = int Array2.array
    
  val enumspec : (int * int, int * IntInf.int list, unit) smlParallel.extspec
  val enum : int -> (int * int) -> unit
  
  val write_enum : int -> int * int -> IntInf.int list -> unit
  val read_enum : int -> int * int -> IntInf.int list
  
end
