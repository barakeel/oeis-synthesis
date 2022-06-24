signature kernel =
sig

  include Abbrev
  (* directory *)
  val selfdir : string 
  val configd : (string ,string) Redblackmap.dict
  
  (* dictionaries shortcut*)
  type ('a,'b) dict = ('a, 'b) Redblackmap.dict
  val dfindo : 'a -> ('a, 'b) dict -> 'b option
  val eaddi : 'a -> 'a Redblackset.set ref -> unit
  val ememi : 'a -> 'a Redblackset.set ref -> bool
  val daddi : 'a -> 'b -> ('a, 'b) dict ref -> unit
  val dmemi : 'a -> ('a, 'b) dict ref -> bool

  (* sequences *)
  type seq = Arbint.int list
  val seq_compare : seq * seq -> order
  val string_of_seq : seq -> string
 
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

  (* definitons *)
  val def_id : int
  val hole_id : int
  val hole : prog
  val inst_pat : prog -> prog list -> prog
  val undef_prog : prog -> prog
  
  (* I/O *)
  val read_progl : string -> prog list
  val write_progl : string -> prog list -> unit
  val read_iprogl : string -> (int * prog) list
  val write_iprogl : string -> (int * prog) list -> unit
  
  (* operators *)
  val operv : term vector
  val maxarity : int
  val arity_of_oper : int -> int
  val name_of_oper : int -> string
  
  (* timer *)
  exception ProgTimeout
  val init_fast_test : unit -> unit
  val init_slow_test : unit -> unit
  val check_timelimit : unit -> unit
  val memsize : int ref
  val incr_timer : unit -> unit
  val skip_counter : int ref
  val init_timer : unit -> unit
  val catch_perror: ('a -> 'b) -> 'a -> (unit -> 'b) -> 'b
  val rt_glob : Timer.real_timer ref
  
end
