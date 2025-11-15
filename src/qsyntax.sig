signature qsyntax = sig
  
  type formula = kernel.prog
  

  (* syntax *)
  val not_id : int
  val or_id : int
  val forall_id : int
  val eq_id : int
  val zero_id : int
  val suc_id : int
  val add_id : int
  
  val is_eq : formula -> bool
  val is_neg : formula -> bool
  val is_varid : int -> bool
  val neg : formula -> formula
  
  (* debugging *)
  val dbg_flag : bool ref
  val dbg_level : int ref
  val dbg : int -> (unit -> string) -> unit
  val hf : formula -> string
  val hfc : formula list -> string
  val fh : string -> formula
  val pe : string -> unit
  
  (* timer *)
  val checktimer : unit -> unit
  val checktimern : int -> unit
  val timed_formula_compare : formula * formula -> order
  
end
