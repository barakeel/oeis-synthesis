signature smt_reader =
sig

  include Abbrev
  
  type finfo = string * int * bool
  type finfox = string * int * bool * string
  
  datatype recfun = 
    Fun0 of unit -> IntInf.int |
    Fun1 of (IntInf.int -> IntInf.int) | 
    Fun2 of (IntInf.int -> IntInf.int -> IntInf.int) | 
    Fun3 of (IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int);

  val dest_fun0 : recfun -> (unit -> IntInf.int)
  val dest_fun1 : recfun -> (IntInf.int -> IntInf.int)
  val dest_fun2 : recfun -> (IntInf.int -> IntInf.int -> IntInf.int)
  val dest_fun3 : recfun -> (IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int)
  
  val reset_cache_glob : (unit -> unit) ref
  val funl_glob : recfun list ref 
  
  val tu : IntInf.int -> IntInf.int
  val tadd : IntInf.int -> IntInf.int -> IntInf.int
  val tmin : IntInf.int -> IntInf.int -> IntInf.int
  val tmul : IntInf.int -> IntInf.int -> IntInf.int
  val tdiv : IntInf.int -> IntInf.int -> IntInf.int
  val tmod : IntInf.int -> IntInf.int -> IntInf.int
  val tleq : IntInf.int -> IntInf.int -> bool

  val unit_compare : unit * unit -> order

  val read_smt_hol : string -> (finfo * term) list
  val read_smt_exec : string -> (finfox * (recfun * (unit -> unit))) list

  val hol_to_progd : (finfo * term) list -> 
    (string, string) Redblackmap.dict

  val fingerprint : recfun * (unit -> unit) -> IntInf.int list option
  val fingerprint_file : string -> string
  
  datatype progx = Insx of ((int * string option) * progx list)
  val hol_to_progxd : (finfo * term) list -> (progx * progx)
  
  val find_subprog_pairs : string -> string
  
end
