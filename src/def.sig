signature def =
sig

  type prog = kernel.prog
  type macro = int list
  type cand = prog * (int * macro)
  
  val random_cand : unit -> macro
  val gen_cand : int -> unit
  val random_def : unit -> macro
  val gen_def : int -> unit
  
  val macro_of_prog : prog -> macro
  val prog_of_macro : macro -> prog
  
  val defv : (macro * int) vector ref
  val read_def : string -> unit
  val read_cand : string -> macro list
  val compress_all_id : macro -> macro
  val expand : macro -> (int, int * int) Redblackmap.dict * macro
  val compress : (int, int * int) Redblackmap.dict * macro -> macro
  val extract_candl : ((int, int * int) Redblackmap.dict * macro) list ->
    cand list
  val check_candl : cand list -> (int * (int * cand) list) list
  
  val mk_def : int -> prog list -> macro list

  val write_itcandl : string -> (int * (int * cand) list) list -> unit
  val read_itcandl : string -> (int * (int * cand) list) list
  val checkspec : (unit, string, (int * (int * cand) list) list)
    smlParallel.extspec
  val parallel_check_def : string -> unit

end
