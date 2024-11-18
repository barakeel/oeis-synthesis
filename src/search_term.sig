signature search_term =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  type seq = kernel.seq
  type ppsisl = string * string list
  
  datatype searchlimit = Visits of int | Seconds of real * real
  val search : term list -> searchlimit -> term list
   
  val smt_operl : term list 
  val search_smt : term list -> real -> term list
  
  val nonesting : bool ref
  val contain_nested : term -> bool
  (* val subtml_glob : term list ref *)
  
  (* z3 calls *)
  val z3_prove : string -> string -> int -> term list -> term list -> bool
  
  (* parse *)
  val pp_to_stringtag : prog * prog -> string
  val stringtag_to_pp : string -> prog * prog
  val parse_ppil : string -> (prog * prog) * term list
  val string_to_ppsisl : string -> ppsisl
  val ppsisl_to_string : ppsisl -> string
  
  (* evaluate a predicate *)
  val create_fed :  prog * prog -> 
    (term, IntInf.int * IntInf.int -> IntInf.int) Redblackmap.dict
  val eval_pred : (term, IntInf.int * IntInf.int -> IntInf.int) Redblackmap.dict ->
    term -> (IntInf.int * IntInf.int) -> bool
  val true_pred : (term, IntInf.int * IntInf.int -> IntInf.int) Redblackmap.dict ->
    term -> bool
  
  (* merging different solutions *)
  val merge : ppsisl list -> ppsisl list -> ppsisl list
  val merge_diff : ppsisl list -> ppsisl list -> ppsisl list
  val merge_simple : ppsisl list -> ppsisl list -> ppsisl list
  
  (* induction axiom *)
  val induct_cj : term -> term
  val random_inductl : prog * prog -> term list
  val random_inductl_string : string -> string
  val ppil_to_string : (prog * prog) * term list -> string
  val z3_prove_inductl : string -> string -> prog * prog -> term list -> string
  val z3_prove_ppil : string -> string
  val z3_prove_para : string -> unit
  
  (* conversion of inductions predicates between term and NMT representations *)
  val inductl_to_stringl : prog * prog -> term list -> string list
  val stringl_to_inductl : prog * prog -> string list -> term list
  
  (* generate random predicates in parallel *)
  val good_pp : prog * prog -> bool
  val gen_init : string -> unit
  val gen_prove_string : string -> string
  val gen_prove_init : string -> unit
  
  (* filter predicates of the same equivalence classes *)
  val z3quotient : string -> string -> term list -> term list
  
end
