signature smt_eval =
sig
  
  type progx = progx.progx
  val subprog_equalities : progx * progx -> (progx * progx) list
   
end
