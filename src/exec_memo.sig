signature exec_memo =
sig

  type seq = kernel.seq
  type prog = kernel.prog
  type exec = IntInf.int list * IntInf.int list -> IntInf.int list
  
  val mk_exec : prog -> exec
  val mk_exec_onev : prog -> (IntInf.int -> IntInf.int)

  (* match oeis *)
  val coverf_oeis : exec -> (int * int) list
  
  (* enumerate *)
  val penum_wtime : int -> prog -> int -> seq
  
  (* verfiy that it is covering an OEIS sequence *)
  val verify_wtime : int -> int * prog -> bool * bool 
  val verify_file : int -> string -> (int * kernel.prog) list

  (* parallel execution *)
  val execspec : (unit, prog list, seq list) smlParallel.extspec
  val parallel_exec : int -> string -> unit
  
end
