signature def =
sig

  type prog = kernel.prog
  type macro = int list
  type cand = prog * (int * macro)
  
  val random_macro : int -> macro
  val create_macrol : int * int * int -> macro list
  val save_macrol : string -> macro list -> unit
  val extract_candl : macro list -> cand list
  val check_candl : cand list -> (int * (int * cand) list) list
  
  val write_itcandl : string -> (int * (int * cand) list) list -> unit
  val read_itcandl : string -> (int * (int * cand) list) list
  val checkspec : (unit, string, (int * (int * cand) list) list)
    smlParallel.extspec
  
  val parallel_check_def : string -> unit
  val boot : string -> int -> int -> unit
  
end
