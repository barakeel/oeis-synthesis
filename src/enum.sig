signature enum =
sig
  
  include Abbrev
  type mat = int Array2.array
  
  val main : int -> int * int -> thm
  val create_pard : int -> int * int -> IntInf.int list -> 
    (IntInf.int, thm) Redblackmap.dict
  
  val enumspec : (int * int, int * IntInf.int list, unit) smlParallel.extspec
  val enum : int -> (int * int) -> unit

  
end
