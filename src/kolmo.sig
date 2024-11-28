signature kolmo =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  type seq = kernel.seq
  
  val nullaryl_glob : (term * (int -> int * int -> int)) list
  val binaryl_glob : (term * (int -> int * int -> int)) list
  val ternaryl_glob : (term * (int -> int * int * int -> int)) list
  
  val kolmo : 
    (term * (int -> int * int -> int)) list *
    (term * (int -> int -> int)) list *
    (term * (int -> int * int -> int)) list *
    (term * (int -> int * int * int -> int)) list -> 
    int -> term list
  
  val kolmo_pp : prog * prog -> int -> term list
  
end
