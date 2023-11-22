signature exec_ctree =
sig

  type seq = kernel.seq
  type prog = kernel.prog
  type cctree = exec_prim.complex exec_prim.ctree
  type exec = cctree * cctree -> cctree
  
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
