signature exec_memo =
sig

  type prog = kernel.prog
  type exec = IntInf.int list * IntInf.int list -> IntInf.int list
  
  val mk_progb : int
  val mk_exec_move : int -> exec list -> exec
  val mk_exec : prog -> exec
  val coverf_oeis : exec -> (int * int) list * int * int list
  val verify_wtime : int -> int * prog -> bool * bool 
  val edgev_glob : (int ref *
       (((int ref * int ref) * (int * int)) vector *
       ((int ref * int ref) * (int * int)) vector)) vector ref 

  (* parallel execution (wip) *)
  val execspec : (unit, kernel.prog list, kernel.seq list) smlParallel.extspec
  val parallel_exec : int -> string -> unit
  
end
