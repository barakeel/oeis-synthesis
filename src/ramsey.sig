signature ramsey =
sig

  val cut : bool Array2.array -> int -> bool Array2.array
  val mk_sym : bool Array2.array -> int -> bool Array2.array
  val invert : bool Array2.array -> int -> bool Array2.array
  
  val all_clique :  bool Array2.array -> int -> int -> int list list

  val ramsey : 
    (int * int -> bool) -> int -> int -> int -> bool Array2.array * int
  val all_charac : bool Array2.array -> int -> (int * int list) list
  val norm_graph : bool Array2.array -> int -> bool Array2.array

end
