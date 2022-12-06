signature def =
sig

  type prog = kernel.prog
  type macro = int list
  type cand = prog * (int * macro)
  
  val random_cand : unit -> macro
  val gen_cand : string -> int -> unit
  val random_def : unit -> macro
  val gen_def : int -> unit
  
  val macro_of_prog : prog -> macro
  val prog_of_macro : macro -> prog
  val string_of_macro : macro -> string
  val macro_of_string : string -> macro
  
  val compress_idl : int list -> int
  val compress_all_idl: int list -> int list
  val expand_id : int -> int list
  val expand_all_id : int list -> int list
  
  val defv : macro vector ref
  val read_def : string -> unit
  val write_def : string -> unit
  val read_cand : string -> macro list
  val unfold_def : macro vector -> macro -> macro
  val defidl_of_defv : macro vector -> (macro * int) list
  val fold_def : (macro * int) list -> macro -> macro 
  val extract_candl : macro list -> cand list
  val check_candl : cand list -> (int * (int * cand) list) list
  
  val progl_of_sol : (int * (int * cand) list) list -> prog list
  val mk_def : int -> prog list -> unit

  val write_itcandl : string -> (int * (int * cand) list) list -> unit
  val read_itcandl : string -> (int * (int * cand) list) list
  val checkspec : (unit, string, (int * (int * cand) list) list)
    smlParallel.extspec
  val parallel_check_def : string -> unit
  val write_gptsol : string -> (int * (int * cand) list) list -> unit

  (* initialization *)
  val itcand_of_itprog : (int * (int * prog) list) -> 
    (int * (int * cand) list)
  val convertto_itcandl : string -> string -> unit

  val init_itcand : string -> int ->  (int * (int * cand) list) list -> unit 
  val init_itprog : string -> int ->  (int * (int * prog) list) list -> unit

end
