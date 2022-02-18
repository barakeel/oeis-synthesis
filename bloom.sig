signature bloom =
sig

  type prog = kernel.prog
  type progi = kernel.progi
  type seq = kernel.seq
  val import_oseq :  unit -> (seq * string) list
  val import_arbseq :  unit ->
    (Arbint.int list * string) list * 
    (Arbint.int list, string list) Redblackmap.dict
  
  val odname : (seq, string list) Redblackmap.dict
  val odv : (seq Redblackset.set) vector
  val find_wins : prog -> seq -> seq list

  val bmod : int
  val badd : seq -> BoolArray.array -> unit
  val bmem : seq -> BoolArray.array -> bool
  
  val bmem_pi : progi -> BoolArray.array -> bool
  val badd_pi : progi -> BoolArray.array -> unit

  val pi_to_hl : progi -> int list
  val bmem_hl : int list -> BoolArray.array -> bool
  val badd_hl : int list -> BoolArray.array -> unit

end
