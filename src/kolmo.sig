signature kolmo =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  type seq = kernel.seq
      
  val kolmo_pp : prog * prog -> int -> term list
  
end
