signature exec_memo =
sig

  type seq = kernel.seq
  type prog = kernel.prog
  type exec = IntInf.int list * IntInf.int list -> IntInf.int list
  
  val mk_exec : prog -> exec
  val mk_exec_onev : prog -> (IntInf.int -> IntInf.int)
  val mk_exec_twov : prog -> (IntInf.int * IntInf.int -> IntInf.int)
    
  (* match oeis *)
  val coverf_oeis : exec -> (int * int) list
  val cover_yenum : prog -> (int * (int * int) list) list
  val coverp_oeis : prog -> (int * int) list
  
  (* enumerate *)
  val penum_wtime : int -> prog -> int -> seq
  
  (* verfiy that it is covering an OEIS sequence *)
  val verify_wtime : int -> int * prog -> bool * bool 
  val verify_file : int -> string -> (int * kernel.prog) list

  (* parallel execution *)
  val execspec : (unit, string, unit) smlParallel.extspec
  val parallel_exec : int -> string list -> unit
  
  (* ramsey *)
  val n_glob : IntInf.int ref
  
  (* arcagi *)
  val mati_glob : int Array2.array ref
  val dimi_glob : (IntInf.int * IntInf.int) ref
  val dimo_glob : (IntInf.int * IntInf.int) ref
  val coliv_glob : int vector ref

  (* parallel b-file checking *)
  val bcheckspec : (unit, int * prog list, string) smlParallel.extspec
  val parallel_bcheck : int -> string -> unit
  
  (* matcher functions *)
  val backv_default : IntInf.int vector
  val backv_glob : IntInf.int vector ref

  (* computing sequences and their hashes *)
  val seqhash_init : string -> string list
  val seqhash_loop : int -> string -> string list -> unit
  (* sorting sequence-program pairs by their sequences *)
  val create_batch_fixed : unit -> ((string * int) list * int) list
  val output_treebatch_fixed : unit -> unit
  val sort_file : string -> unit
  
end
