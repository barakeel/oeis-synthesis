signature ramsey =
sig

  val mk_sym : bool Array2.array -> int -> bool Array2.array

  val ramsey : 
    (int * int -> bool) -> int -> int -> int -> bool Array2.array * int
  val all_charac : bool Array2.array -> int -> (int * int list) list
  val norm_graph : bool Array2.array -> int -> bool Array2.array

end
