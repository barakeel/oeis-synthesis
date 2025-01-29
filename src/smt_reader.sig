signature smt_reader =
sig

  include Abbrev
  
  type finfo = string * int * bool
  type prog = kernel.prog
  type progx = progx.progx
  type sexp = sexp.sexp
    
  (* re-translate a equality between programs to smt *)
  val share_flag : bool ref
  val eq_flag : bool ref
  val imp_flag : bool ref
  val retranslate : string -> string -> unit
  
  (* checks that a retranslation would produce the same problem *)
  val check_no_change : string -> unit
  
  (* write a SMT problem with optional induction instances *)
  val create_decl_only2 : prog * prog -> term list
  val create_decl_only : prog * prog -> term list
  val create_decl : prog * prog -> term list
  val write_induct_pb : string -> term list -> term list -> unit
  val skpb_of_pp : (prog * prog) * term list -> term list
  
end
