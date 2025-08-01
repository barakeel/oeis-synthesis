signature kernel =
sig

  include Abbrev
  (* directory *)
  val selfdir : string 
 
  (* flags *)
  val configd : (string ,string) Redblackmap.dict
  val bflag : string -> bool ref
  val seq_flag : bool ref (* allow to call the sequence *)
  val z_flag : bool ref (* functions of arity 3 *)
  val t_flag : bool ref (* optimize for time instead of size *)
  val nomerge_flag : bool ref (* keep all solutions *)
  val sol2_flag : bool ref (* train on smallest and fastest solutions *)
  val solm_flag : bool ref
  val pareto_flag : bool ref
  val pareto_number : int
  val optimal_flag : bool ref
  val optimalonly_flag : bool ref
  val optimal_coeff : real
  val notarget_flag : bool ref (* train without looking at the target *)
  val array_flag : bool ref
  val beam_flag : bool ref
  val beam_width : int
  val stop_flag : bool ref
  val newseq_flag : bool ref
  val extranum_flag : bool ref
  val locsearch_flag : bool ref
  val halfnoise_flag : bool ref
  val minimal_flag : bool ref
  val partial_flag : bool ref
  val extra_flag : bool ref
  val dim_glob : int 
  val train_multi : int ref (* train multiple tnn at the same time *)
  val fs_flag : bool ref (* experiment with find_stat *)
  val turing_flag : bool ref (* experiment using a turing machine *)
  val rps_flag : bool ref (* rock-paper-scissor experiment *)
  val think_flag : bool ref (* experiments with thinking tokens *)
  val run_flag : bool ref (* experiments with running subprograms *)
  val her_flag : bool ref  
  val intl_flag : bool ref 
  val num_epoch : int
  val learning_rate : real
  val init_timeincr : int
  val short_timeincr : int
  val long_timeincr : int
  val temperature : real
  val memo_flag : bool ref
  val memo_number : int
  val ctree_flag : bool ref
  val wrat_flag : bool ref
  val maxproglen : int
  val maxproglen_treesearch : int
  val maxint_flag : bool ref
  val maxintsize : int
  val reprocess_flag : bool ref
  val reverse_nmtoutput : bool ref
  val select_cluster : bool ref
  val select_random : bool ref
  val select_number : int
  val reprocess_select_flag : bool ref
  val nooeis_flag : bool ref
  val revamp_flag : bool ref
  val push_limit : int
  val prnn_flag : bool ref
  val prnnsum_flag : bool ref
  val prnnsum_limit : int
  val prnntim : int
  val prnnwidth : int
  val veggy_flag : bool ref
  val arcagi_flag : bool ref
  val smt_flag : bool ref
  val nooeisdata_flag : bool ref
  val noimp_flag : bool ref
  val imp_filter : bool ref
  val subz_flag : bool ref
  val disable_eval : bool ref
  val disable_minimize : bool ref
  val disable_shuffle : bool ref
  val mydebug : bool ref
  val fo_flag : bool ref
  val skolemize_flag : bool ref
  val cnf_flag : bool ref
  val split_conj_flag : bool ref
  val oneline_flag : bool ref
  val altaxiom_flag : bool ref
  val matchback_flag : bool ref
  val yenum_flag : bool ref
  
  (* flags not read from config *)
  val expname : string ref
  val ngen_glob : int ref
  
  (* dictionaries shortcut*)
  type ('a,'b) dict = ('a, 'b) Redblackmap.dict
  val dfindo : 'a -> ('a, 'b) dict -> 'b option
  val eaddi : 'a -> 'a Redblackset.set ref -> unit
  val ememi : 'a -> 'a Redblackset.set ref -> bool
  val daddi : 'a -> 'b -> ('a, 'b) dict ref -> unit
  val dmemi : 'a -> ('a, 'b) dict ref -> bool
  val ereml : 'a list -> 'a Redblackset.set -> 'a Redblackset.set
  val dreml : 'a list -> ('a,'b) dict -> ('a,'b) dict
  
  (* useful tools *)
  val range : int * int * (int -> 'a) -> 'a list
  val subsets_of_size : int -> 'a list -> 'a list list
  val infts : IntInf.int -> string
  val stinf : string -> IntInf.int
  val streal : string -> real
  val stil : string -> int list
  val ilts : int list -> string
  val timer_glob1 : real ref
  val timer_glob2 : real ref
  val timer_glob3 : real ref
  val timer_glob4 : real ref
  val timer_glob5 : real ref
  val inv_cmp : ('a * 'b -> 'c) -> 'b * 'a -> 'c
  val string_of_var : term -> string
  val length_geq : 'a list -> int -> bool
  val length_eq : 'a list -> int -> bool
  val first_diff : ('a * 'a -> order) -> 'a list -> 'a list -> ('a * 'a) option
  val compare_term_size : term * term -> order
  val hashMod : int -> string -> int
  val split_pair : char -> string -> string * string
  val append_endline_lock : string -> string -> unit
  val appendl : string -> string list -> unit
  val bare_readl_app : (string -> unit) -> string -> unit
  
  (* sequences *)
  type seq = IntInf.int list
  type anum = int
  val target_glob : seq ref
  val targetn_glob : int ref
  val seq_compare : seq * seq -> order
  val string_of_seq : seq -> string
  val seq_of_string : string -> seq
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
  val contain_id : int -> prog -> bool
  val contain_opers : string -> prog -> bool 
  val zeroy : prog -> prog
  (* solutions *)
  type sol = anum * (int * prog) list
   
  (* I/O *)
  val read_proglrl : string -> (prog list * real) list
  val write_proglrl : string -> (prog list * real) list -> unit
  val read_itprogl : string -> sol list
  val write_itprogl : string -> sol list -> unit
  
  val read_progl : string -> prog list
  val write_progl : string -> prog list -> unit
  val read_seql : string -> seq list
  val write_seql : string -> seq list -> unit
  
  (* operators *)
  val operv : term vector
  val maxmove : int
  val arity_of_oper : int -> int
  val name_of_oper : int -> string
  val oper_of_name : string -> int
  val ho_ariv : int vector
  val x_id : int
  val y_id : int
  
  (* timer *)
  exception ProgTimeout
  val graph : (IntInf.int * int) list ref
  val graphb : int ref
  val abstimer : int ref
  val max_compr_number : int ref
  val timeincr : int ref
  val timelimit : int ref
  val push_counter : int ref
  val init_fast_test : unit -> unit
  val init_slow_test : unit -> unit
  val incr_timer : unit -> unit
  val init_timer : unit -> unit
  val catch_perror: ('a -> 'b) -> 'a -> (unit -> 'b) -> 'b 
  val eval_option : ('a -> 'b) -> 'a -> 'b option
  val map_total : ('a -> 'b option) -> 'a list -> 'b list option
  
  (* gpt *)
  val gpt_of_seq : seq -> string  
  val gpt_of_id : id -> string
  val gpt_of_prog : prog -> string
  val id_of_gpt : string -> id
  val tokenl_of_gpt : string -> int list
  val prog_of_gpt : string -> prog
  val prog_of_gpt_err : string -> prog
  
  val tokenl_of_prog : prog -> int list
  val prog_of_tokenl : int list -> prog
  
  (* other *)
  val prog_of_movel : int list -> prog
  val prog_of_movelo  : int list -> prog option
  
  (* seqprog *)
  val seqprog_flag : bool ref
  val write_seqprog : string -> (seq * prog) list -> unit
  val read_seqprog : string -> (seq * prog) list
  val write_anumprog : string -> (anum * prog) list -> unit
  val read_anumprog : string -> (anum * prog) list
  
  (* pgen experiment *)
  type pgen = prog * (int * prog) list
  val pgen_flag : bool ref
  val pgen_operl : (string * int) list
  val read_pgen : string -> pgen list
  val write_pgen : string -> pgen list -> unit
  
  (* ramsey experiment *)
  val ramsey_flag : bool ref
  type ramsey = (int * prog) * (int * int * int * int)
  val write_ramseyl : string -> ramsey list -> unit
  val read_ramseyl : string -> ramsey list

  (* hanabi experiment *)
  val hanabi_flag : bool ref
  val hanabi_short : bool ref
  val rams_flag : bool ref
  val rams_short : bool ref
  val rams_noloop : bool ref
  val rams_diff : bool ref
  val rams_double : bool ref
  val rams_dnf : bool ref
  val rams_nicer : bool ref
  val nauto_check : bool ref
  type hanabi = (int * prog) * IntInf.int
  val write_hanabil : string -> hanabi list -> unit
  val read_hanabil : string -> hanabi list
  
  
  (* arcagi experiment *)
  type arcagi = int * prog * bool * int
  val write_arcagil : string -> arcagi list -> unit
  val read_arcagil : string -> arcagi list

  (* parallelization of function of the type string to string *)
  val stringspec_fun_default : string -> string
  val stringspec_fun_glob : (string -> string) ref
  val stringspec_funname_glob : string ref
  val stringspec : (unit, string, string) smlParallel.extspec
  val parmap_sl : int -> string -> string list -> string list
  val test_fun : string -> string

end
