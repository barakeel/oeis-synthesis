signature enum =
sig
  
  include Abbrev
  type mat = int Array2.array
  
  val main : int -> (int * int) -> thm
  
end
