signature synt =
sig

val parse_seq : string -> int list
val synt : real -> int -> int list -> kernel.prog option
val add_gap : int -> unit

end
