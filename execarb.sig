signature execarb =
sig

  val aod : (Arbint.int list, string list) Redblackmap.dict
  val maxarb : Arbint.int
  val mk_aodnv : int -> Arbint.int list Redblackset.set vector
  val arb_seq_of_prog : int -> kernel.prog -> Arbint.int list
  val minlength : int ref
  val mininfo : real ref 
  val longereq : int -> 'a list -> bool
  val number_seq : kernel.prog list -> int -> int

end
