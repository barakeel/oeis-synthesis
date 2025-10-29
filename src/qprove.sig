signature qprove = sig
    
  include Abbrev
  
  type prog = kernel.prog
  type formula = kernel.prog
  type qprove = (formula list * (prog * int))
  type state = prog list
  type exec = state * state -> state
  type branch = {have : prog Redblackset.set, havel : prog list,  
                 pending : prog list}
  
  val dbg_flag : bool ref
  
  val or : prog -> prog -> prog
  val var : int -> prog
  val neg : prog -> prog
  val forall : prog -> prog -> prog
  
  val action_flag : bool ref
  val actionf_glob : (branch -> formula list) ref
  val prove : prog list -> prog -> bool
  val refute : prog list -> bool
  
  val timedv : (exec list -> exec) vector
  val mk_exec : prog -> exec
  
  val error_count : int ref
  val timeout_count : int ref
  val sat_count : int ref
  val unsat_count : int ref
  val qprove : prog -> (formula * int) -> (bool * int)
  val qprove_asm : prog -> ((formula list * formula) * int) -> (bool * int)
  val qprove_baseline : prog -> (bool * int)
  
  val read_true_exl : string -> term list
  val htt : term -> prog
  
  val human_formula : formula -> string
  val formula_human : string -> formula
  
  val string_of_formula : formula -> string
  val formula_of_string : string -> formula
  val create_benchmark8 : string -> formula list -> unit
  
  val checkinit_qprove : unit -> unit
  val checkfinal_qprove : unit -> (formula list * (prog * int)) list
  val checkonline_qprove : prog -> unit
  val merge_qprove : qprove list -> string option -> qprove list
  val formulal_glob : (formula * int) list list ref
  val init_formulal_glob : unit -> unit
  
  val human_qprove_one : qprove -> string
  val write_qprove : string -> qprove list -> unit
  val read_qprove : string -> qprove list
  
  val axiom1: formula
  val axiom2: formula
  val axiom3: formula
  
  
end
