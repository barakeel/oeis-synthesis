signature enum =
sig
  
  include Abbrev
  type mat = int Array2.array
  
  val main : int -> (int * int) -> thm
  val enumspec : (unit, (int * IntInf.int list), unit) smlParallel.extspec
  val start44 : int -> unit
  
end
