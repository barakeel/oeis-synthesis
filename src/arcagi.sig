signature arcagi =
sig
  
  include Abbrev
  
  val read_ex : string ->
    (real Array2.array * real Array2.array) list *
    (real Array2.array * real Array2.array) list
  
  val match_output : (int * int -> int) -> int Array2.array -> bool * int
  val compute_output : (int * int -> int) -> int Array2.array
  
end
