signature kernel =
sig

  include Abbrev
  (* directory *)
  val selfdir : string 
  
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
  val depend_on_x : prog -> bool
  val depend_on_y : prog -> bool
  
  (* I/O *)
  val read_progl : string -> prog list
  val write_progl : string -> prog list -> unit
  val read_iprogl : string -> (int * prog) list
  val write_iprogl : string -> (int * prog) list -> unit

  (* operators *)
  val operv : term vector
  val arity_of_oper : int -> int
  val name_of_oper : int -> string
  
  (* timer *)
  exception ProgTimeout
  val timelimit : real ref
  val rt_glob : Timer.real_timer ref
  
  
end
