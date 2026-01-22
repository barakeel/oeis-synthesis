signature qsyntax = sig
  
  type id = int * int
  datatype formula = A of (id * formula list) 
  datatype formulat = At of (id * bool * formulat list) 
  
  val infix_flag : bool ref
  
  (* timer *)
  val checktimer : unit -> unit
  val checktimern : int -> unit

  (* syntax *)
  val not_id : id
  val or_id : id
  val forall_id : id
  val eq_id : id
  val add_id : id
  val diff_id : id
  val mult_id : id
  val div_id : id
  val mod_id : id
  val loop2_id : id
  val loop2h_id : id
  val is_varid : id -> bool
  val is_skolemid : id -> bool
  val id_compare : id * id -> order
  
  val is_num : formula -> bool
  val is_eq : formula -> bool
  val is_neg : formula -> bool
  val is_boolean : formula -> bool
  val neg : formula -> formula
  val formula_compare : formula * formula -> order
  val formula_compare_size : formula * formula -> order
  val formula_size : formula -> int
  val zero : formula
  val one : formula
  val mk_eq : formula * formula -> formula
  val mk_geq : formula * formula -> formula
  val mk_add : formula * formula -> formula
  val mk_mult : formula * formula -> formula
  val mk_diff : formula * formula -> formula
  val mk_var : int -> formula
  val mk_int : int -> formula
  val prog_to_formula : kernel.prog -> formula
  
  val dest_eq : formula -> formula * formula
  val eqf : (formula -> formula) -> formula -> formula
  val lhf : (formula -> formula) -> formula -> formula
  val rhf : (formula -> formula) -> formula -> formula
  
  val mk_exec_at : formulat -> exec.exec
  val eval : formula -> formula
  
  
  val fresh_var : unit -> formula
  val reset_var_counter : unit -> unit

  
  (* debugging *)
  val dbg_flag : bool ref
  val dbg_level : int ref
  val dbg : int -> (unit -> string) -> unit
  val hf : formula -> string
  val hfc : formula list -> string
  val fh : string -> formula
  val pe : string -> unit

  (* cnf *)
  val reset_skolem_counter : unit -> unit
  val fresh_skolemid : unit -> (int * int)
  
  val subst_one : id * formula -> formula -> formula
  val substl : (id * formula) list -> formula -> formula
  val CNF : formula -> formula list list
  
end
