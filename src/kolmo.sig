signature kolmo =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  type seq = kernel.seq

  val extra_nullaryl_glob : term list ref 
  val kolmo_pp : prog * prog -> int -> term list
  val kolmo_pp_exact : prog * prog -> int -> term list
  
end
