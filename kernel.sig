signature kernel =
sig

  include Abbrev
  (* directory *)
  val selfdir : string 
  
  (* globals *)
  val maxinput : int ref

  (* types *)
  val error : int
  type oper2 = int * int -> int
  type oper3 = int * int * int -> int
  type exec = int * int -> int  
  type seq = int list
  val seq_compare : seq * seq -> order
  val string_of_seq : seq -> string
 
  (* program *)
  type id = int
  datatype prog = Ins of (id * prog list)
  val prog_compare : prog * prog -> order
  val equal_prog : prog * prog -> bool
  val prog_size : prog -> int
  val all_subprog : prog -> prog list
  val depend_on_i : prog -> bool
  val under_lambda : prog -> prog list  
  val has_lambdai : prog -> bool
  val has_loop2 : prog -> bool
  val shift_prog : int -> prog -> prog
  val same_sem : prog -> prog -> bool  
  val all_holes : prog -> prog list
  val inst_pat : prog -> prog list -> prog
  val psubst : (prog * int) -> prog -> prog 
  val psubstl : (prog * int) list -> prog -> prog 
  val read_progl : string -> prog list
  val write_progl : string -> prog list -> unit

  (* compressed programs *)
  type progi = Arbint.int
  val progi_compare : progi * progi -> order
  val equal_progi : progi * progi -> bool
  val zip_prog : prog -> progi
  val unzip_prog : progi -> prog
  val pi_to_hseq : progi -> int list

  (* pretty printing *)
  val constnorm_flag : bool ref
  val polynorm_flag : bool ref
  val humanf : prog -> string
  val humani : int -> prog -> string
  val rm_par : string -> string

  (* inputs *)
  val entryl : (int * int) list

  (* execute program *)
  val timelimit : int ref (* todo increase the time limit when testing *)
  val compose2 : oper2 -> exec -> exec -> exec
  val compose3 :  oper3 -> exec -> exec -> exec -> exec 
  val counter : int ref
  val start : ('a -> 'b) -> 'a -> 'b
 
  (* instructions *)
  val zero_f : exec
  val zero_id : id
  val one_f : exec
  val one_id : id
  val two_f : exec
  val two_id : id
  val addi_f : oper2
  val addi_id : id
  val diff_f : oper2
  val diff_id : id
  val mult_f : oper2
  val mult_id : id
  val divi_f : oper2
  val divi_id : id
  val modu_f : oper2
  val modu_id : id
  val cond_f : oper3
  val cond_id : id  
  val loop_f : exec -> oper2
  val loop_id : id
  val var_f : exec
  val var_id : id
  val ind_f : exec
  val ind_id : id
  val compr_f : exec -> int -> int
  val compr_id : id
  val loop2_f : exec -> exec -> int -> int
  val loop2_id : id
  val def_id : id

  (* associate id and function *)
  val nullaryl : (id * exec) list
  val nullaryidl : id list
  val is_nullary : id -> bool
  val find_nullaryf : id -> exec
  val binaryl : (id * oper2) list
  val binaryidl : id list
  val is_binary : id -> bool
  val find_binaryf : id -> oper2
  val binaryidl_nocomm : id list
  val is_comm : id -> bool
  
  (* definitions *)
  val nbest_def : int -> prog list -> (prog * int) list * prog list
  val defl : (int * prog) list
  val defd : (int, prog list -> prog) Redblackmap.dict
  val undef_prog : prog -> prog

  (* create executable from program *)
  val mk_exec : prog -> (int * int) -> (int * int)
  
  val semo_of_prog : prog -> seq option
  val semtimo_of_prog : prog -> (seq * int) option
  val sem_of_prog : prog -> seq
  val seq_of_prog : prog -> seq
  
  val is_executable : prog -> bool

  val operv : term vector
  val arity_of_oper : int -> int
  val name_of_oper : int -> string
  
  (* search time limit *)
  exception SearchTimeout;
  val rti_glob : int ref
  val search_time : Time.time ref
  val search_steps : int ref
  val init_timer : unit -> unit
  val check_timer : unit -> unit

end
