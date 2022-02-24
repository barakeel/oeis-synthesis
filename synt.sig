signature synt =
sig

val parse_seq : string -> int list
val synt : real -> int list -> kernel.prog option
val seq : int -> kernel.prog -> unit

end
