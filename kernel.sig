signature kernel =
sig

  include Abbrev
  (* directory *)
  val selfdir : string 

  (* globals *)
  exception ProgTimeout
  val timelimitarb : real ref
  val rt_glob : int
  val overflow : int
  val maxinput : int

  (* types *)
  type exec = int * int -> int 
  type oper = exec list -> exec
  
  (* sequence *)
  type seq = int list
  val seq_compare : seq * seq -> order
  val string_of_seq : seq -> string
 
  (* program *)
  type id = int
  datatype prog = Ins of (id * prog list)
  val raw_prog : prog -> string
  val prog_compare : prog * prog -> order
  val equal_prog : prog * prog -> bool
  val prog_size : prog -> int
  val prog_compare_size : prog * prog -> order
  val progl_size : prog list -> int
  val progl_compare_size : prog list * prog list -> order

  val all_subprog : prog -> prog list
  val depend_on_y : prog -> bool
  val read_progl : string -> prog list
  val write_progl : string -> prog list -> unit
  val read_iprogl : string -> (int * prog) list
  val write_iprogl : string -> (int * prog) list -> unit

  (* operators *)
  val operv : term vector
  val arity_of_oper : int -> int
  val name_of_oper : int -> string
  
  (* evaluate a program on a defined list of inputs *)
  val entrylx : (int * int) list
  val entrylxy : (int * int) list
  val semo_of_prog : bool -> (int * int) list -> prog -> (int list * int) option
  
  
  
end
