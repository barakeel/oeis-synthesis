signature smt_eval =
sig
  
  type prog = kernel.prog
  type progx = progx.progx
  
  (*
  val subprog_equalities : progx * progx -> (progx * progx) list
  val subprog_eq_list : (string * (prog * prog)) list ->
        (string * (prog * prog)) list
  *)
  val fingerprint_px : progx -> IntInf.int option list
  val match_fingerprint : IntInf.int option list * IntInf.int option list -> bool
  
  val fingerprint_loop : progx -> IntInf.int option list list
  val match_loop : (progx * IntInf.int option list list) * 
                   (progx * IntInf.int option list list) -> bool
  
end
