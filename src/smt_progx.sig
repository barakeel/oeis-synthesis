signature smt_progx =
sig

  include Abbrev
  
  type finfo = string * int * bool
  type prog = kernel.prog
  type progx = progx.progx
  type sexp = sexp.sexp
  
  (* hol terms to program equality *)
  val hol_to_progxpair : (finfo * term) list -> progx * progx
  
  (* sub-program to hol terms *)
  val pxx_to_hol_aux : progx -> term
  val pxx_to_hol : progx -> term list
  val arity_of_progx : progx -> int
  val get_recfl : progx * progx -> term list
  val get_recfpl : progx * progx -> (term * prog) list
  val auto_comb : string * term list -> term
  
  (* definition for loop2_snd *)
  val get_recfl_ws : progx * progx -> term list
  val add_sdecl : term list -> term list
  val get_recfpl_ws : progx * progx -> (term * prog) list
  
  (* extra equalities for equality congruence (on px not pxx) *)
  val eq_loop : progx * progx -> term list
  val eq_loop_imp : progx * progx -> term list
  val eq_compr : progx * progx -> term list
  val eq_compr_imp : progx * progx -> term list
  val eq_loop2_1 : progx * progx -> term list
  val eq_loop2_2 : progx * progx -> term list
  val eq_loop2_imp : progx * progx -> term list

  (* inferring pairs of programs from SMT file *)
  val read_smt_progpair : string -> prog * prog
  val read_smt_progxpair : string -> progx * progx
  
  (* writing/reading program pair for each OEIS sequence *)
  val write_anumprogpairs : string -> (string * (prog * prog)) list -> unit
  val read_anumprogpairs : string -> (string * (prog * prog)) list
  
end
