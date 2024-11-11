signature search_term =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  type seq = kernel.seq
 
  datatype searchlimit = Visits of int | Seconds of real * real
  val search : term list -> searchlimit -> term list
   
  val smt_operl : term list 
  val search_smt : term list -> real -> term list
  
  val subtml_glob : term list ref
  
  (* z3 calls *)
  val z3_prove : string -> string -> int -> term list -> term list -> bool
  
  (* induction axiom *)
  val induct_cj : term -> term
  val get_inductl : real -> prog * prog -> term list
  val z3_prove_inductl : string -> string -> prog * prog -> string
  val z3_prove_anum : string -> string
  
  (* conversion of inductions predicates between term and NMT representations *)
  val inductl_to_stringl : prog * prog -> term list -> string list
  val stringl_to_inductl : prog * prog -> string list -> term list
  
  (* filter out the 3 problems that have too many macros *)
  val good_pp : prog * prog -> bool

end

