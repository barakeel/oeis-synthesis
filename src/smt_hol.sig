signature smt_hol =
sig

  include Abbrev
  
  type finfo = string * int * bool
  type prog = kernel.prog
  type progx = progx.progx
  type sexp = sexp.sexp
  
  (* read a SMT file *)
  val smt_to_hol : sexp -> term
  val read_smt_sexp : string -> sexp list
  val read_smt_hol : string -> (finfo * term) list
  
  (* write a SMT file *)
  val hol_to_smt : term -> sexp
  val get_decl : term list -> string list
  val get_decl_md : term list -> string list
  val get_assertl : term list -> string list
  val write_hol_smt : string -> string list -> term list -> string list -> unit 
  
end
