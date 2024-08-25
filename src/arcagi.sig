signature arcagi =
sig
  
  include Abbrev
  
  val read_ex : string ->
    (real Array2.array * real Array2.array) list *
    (real Array2.array * real Array2.array) list
  
end
