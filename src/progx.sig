signature progx =
sig

  include Abbrev
  type prog = kernel.prog
  
  (* definition *)
  datatype progx = Insx of ((int * string option) * progx list)
  val progx_compare : progx * progx -> order
  val progx_size : progx -> int
  val progx_compare_size : progx * progx -> order
  val name_progx : string * progx -> progx
  val unname_progx : progx -> progx
  val progx_to_string : progx -> string
  
  (* convert between prog and progx *)
  val progx_to_prog : progx -> prog
  val progxpair_to_progpair : (progx * progx) -> (prog * prog)
  val prog_to_progx : prog -> progx
  val progpair_to_progxpair : (prog * prog) -> (progx * progx)
  val progpair_to_progxpair_shared : (prog * prog) -> (progx * progx)
  
  (* naming arguments of subloops *)  
  val progx_to_progxx : progx -> progx

  (* collecting subprograms *)
  val filter_subprog : (progx -> bool) -> progx -> progx list
  val all_subloop : progx -> progx list
  val all_subcompr : progx -> progx list
  val all_subloop2 : progx -> progx list
  val all_subnamed : progx -> progx list
  val all_subprog : progx -> progx list
  
  (* collecting higher-order arguments *)
  val hoarg_loop : progx -> (progx * string)
  val hoarg_compr : progx -> (progx * string)
  val hoarg_loop2 : progx -> ((progx * progx) * string)
  
  
end
