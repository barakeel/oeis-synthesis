signature smt_eval =
sig
  
  type prog = kernel.prog
  type progx = progx.progx
  val subprog_equalities : progx * progx -> (progx * progx) list
  val subprog_eq_list : (string * (prog * prog)) list ->
        (string * (prog * prog)) list
   
end
