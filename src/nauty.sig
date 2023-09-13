signature nauty =
sig

  val refine_partition : int list list -> int list list list
  val normalize_nauty : int Array2.array -> int Array2.array
  val normalize_nauty_safe : int Array2.array -> int Array2.array

end
