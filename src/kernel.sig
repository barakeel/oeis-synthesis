signature kernel =
sig

  include Abbrev
  (* directory *)
  val selfdir : string 
 
  (* flags *)
  val configd : (string ,string) Redblackmap.dict
  val bflag : string -> bool ref
  val t_flag : bool ref (* optimize for time instead of size *)
  val z_flag : bool ref (* functions of arity 3 *)
  val sol2_flag : bool ref (* train on smallest and fastest solutions *)
  val notarget_flag : bool ref (* train without looking at the target *)
  val prime_flag : bool ref (* train targeting only prime approximations *)
  val hadamard_flag : bool ref
  val local_flag : bool ref
  val array_flag : bool ref
  val sqrt_flag : bool ref
  val loop_flag : bool ref
  val bigvar_flag : bool ref
  val convolution_flag : bool ref
  val family_flag : bool ref
  val beam_flag : bool ref
  val stop_flag : bool ref
  val newseq_flag : bool ref
  val extranum_flag : bool ref
  val locsearch_flag : bool ref
  val halfnoise_flag : bool ref
  val subprog_flag : bool ref
  val slowcheck_flag : bool ref
  val minimal_flag : bool ref
  val ramsey_flag : bool ref
  val fs_flag : bool ref
  val partial_flag : bool ref
  val extra_flag : bool ref
  
  val use_ob : bool ref
  val dim_glob : int ref   

  (* dictionaries shortcut*)
  type ('a,'b) dict = ('a, 'b) Redblackmap.dict
  val dfindo : 'a -> ('a, 'b) dict -> 'b option
  val eaddi : 'a -> 'a Redblackset.set ref -> unit
  val ememi : 'a -> 'a Redblackset.set ref -> bool
  val daddi : 'a -> 'b -> ('a, 'b) dict ref -> unit
  val dmemi : 'a -> ('a, 'b) dict ref -> bool

  (* sequences *)
  type seq = IntInf.int list
  type anum = int
  val target_glob : seq ref
  val seq_compare : seq * seq -> order
  val string_of_seq : seq -> string
  val is_prefix : seq -> seq -> bool
  
  (* programs *)
  type id = int
  datatype prog = Ins of (id * prog list)
  val raw_prog : prog -> string
  val prog_compare : prog * prog -> order
  val equal_prog : prog * prog -> bool
  val prog_size : prog -> int
  val prog_compare_size : prog * prog -> order
  val all_subprog : prog -> prog list
  val all_subcompr : prog -> prog list
  val depend_on_x : prog -> bool
  val depend_on_y : prog -> bool
  val depend_on_z : prog -> bool
  val is_constant : prog -> bool
  val contain_arr2 : prog -> bool
  val contain_arr1 : prog -> bool
  (* solutions *)
  type sol = anum * (int * prog) list
   
  (* I/O *)
  val read_progl : string -> prog list
  val write_progl : string -> prog list -> unit
  val read_proglr : string -> (prog list * real)
  val write_proglr : string -> (prog list * real) -> unit
  val read_proglrl : string -> (prog list * real) list
  val write_proglrl : string -> (prog list * real) list -> unit
  val read_iprogl : string -> (int * prog) list
  val write_iprogl : string -> (int * prog) list -> unit
  val read_itprogl : string -> sol list
  val write_itprogl : string -> sol list -> unit
  val read_primel : string -> (seq * (int * prog)) list
  val write_primel : string -> (seq * (int * prog)) list -> unit
  type ramsey = (int * prog) * (int * int * int * int)
  val read_ramseyl : string -> ramsey list
  val write_ramseyl : string -> ramsey list -> unit
  
  (* operators *)
  val operv : term vector
  val maxmove : int
  val arity_of_oper : int -> int
  val name_of_oper : int -> string
  
  (* timer *)
  exception ProgTimeout
  val graph : (IntInf.int * int) list ref
  val graphb : int ref
  val abstimer : int ref
  val max_compr_number : int ref
  val timeincr : int ref
  val timelimit : int ref
  val short_timeincr : int
  val init_fast_test : unit -> unit
  val long_timeincr : int
  val init_slow_test : unit -> unit
  val incr_timer : unit -> unit
  val init_timer : unit -> unit
  val catch_perror: ('a -> 'b) -> 'a -> (unit -> 'b) -> 'b 
  
  (* gpt *)
  val gpt_of_seq : seq -> string  
  val gpt_of_id : id -> string
  val gpt_of_prog : prog -> string
  val id_of_gpt : string -> id
  val movel_of_gpt : string -> id list
  val prog_of_gpt : string -> prog
  
  (* hadamard matrices *)
  val sqrtv : int vector vector
  val invv : int vector vector
  val leastdivv : int vector  

end
