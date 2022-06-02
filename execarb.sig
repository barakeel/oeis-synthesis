signature execarb =
sig

  type prog = kernel.prog
  
  val large_arb : Arbint.int -> bool
  
  val mk_execarb : prog -> Arbint.int * Arbint.int -> Arbint.int
 
  val coverp_oeis : prog -> int list * int * int list
  val coverp_target : prog -> Arbint.int list -> bool
 
  val penum : prog -> int -> Arbint.int list
  
  (* compr cache *)
  val cache : (kernel.prog, Arbint.int vector) Redblackmap.dict ref
  val clean_cache : unit -> unit
  
  (* oeis cache *)
  val ocache : (kernel.prog, Arbint.int vector) Redblackmap.dict ref
  val add_ocache : prog -> unit
  
  
  
end
