signature execarb =
sig

val aod : (Arbint.int list, string list) Redblackmap.dict
val maxarb : Arbint.int
val mk_aodnv : int -> Arbint.int list Redblackset.set vector
val arb_seq_of_prog : int -> kernel.prog -> Arbint.int list

end
