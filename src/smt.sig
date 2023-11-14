signature smt =
sig

  type prog = kernel.prog
  
  val anum_of_string : string -> int
  val write_anuml : string -> int list -> unit
  val export_smt2 : bool -> string -> string -> unit
  val export_smt2_anuml : bool -> int list -> string -> string -> unit
  
  (* looking for inductive problems *)
  val test_syn : prog -> bool
  val test_sem : prog -> bool
  val ind_pb : (prog -> bool) -> (int * (prog * prog)) list -> int list
  
end
