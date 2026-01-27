signature qlang = sig
  
  type formula = qsyntax.formula
  type goal = formula list * formula
  type tactic = goal list -> goal list
  exception Error
  exception Proof
  
  val x_flag : bool ref (* tells if we know if x0 is nonnegative *)
  
  val replace_atl : (formula -> formula) -> formula -> formula
  val unfold : formula -> formula
  val unfold_num : formula -> formula
  val decouple : formula -> formula

  val replace_id : qsyntax.id * qsyntax.id -> formula -> formula
  val repeat : (''a -> ''a) -> ''a -> ''a
    
  (* normalizations *)
  val formula_to_poly : formula -> (formula list * int) list
  val poly_to_formula : (formula list * int) list -> formula
  val norm_poly : formula -> formula
  
  val simp : formula -> formula
  
  (* generalizations *)
  val gen_idloop : formula -> formula
  
  (* pattern match *)
  val constant_loop2h : formula -> formula
  
  (* parsing problems *)
  val get_problems : unit -> (string * goal list) list

  (* helpers *)
  val replace : formula * formula -> formula -> formula
  val replace_asm : int -> tactic
  
  (* chooses a subterm of a formula *)
  val s1 : 'a list -> 'a
  val s2 : 'a list -> 'a
  val s3 : 'a list -> 'a
  val s4 : 'a list -> 'a
  val s5 : 'a list -> 'a
  val arg : formula -> formula list

  (* goal based primitives *)
  val def_one : formula -> formula
  val undef_one : formula -> formula
  
  val apply_concl : (formula -> formula) -> tactic
  val apply_asm : (formula -> formula) -> tactic
  val apply_all : (formula -> formula) -> tactic
  
  val pg : goal -> unit 
  val pgl : goal list -> unit
  val induct : tactic
  val induct2 : tactic
  val induct2_2 : tactic
  val refl : tactic (* could be automatic *)
  val drop_asm : tactic
  val auto : tactic
  val imitate : tactic
  
  val argf : int -> (formula -> formula) -> formula -> formula 
  val apply_asmk : int -> (formula -> formula) -> tactic
  val addzero_asmk_left : int -> tactic
   
  val stack : goal list list ref 
  val e : tactic -> unit
  val init_proof : goal list -> unit
  val ac : (formula -> formula) -> tactic
  val aa : (formula -> formula) -> tactic
  val aall : (formula -> formula) -> tactic
  val poly : formula -> formula
  val >> : tactic * tactic -> tactic
  
  val is_proof: tactic -> goal list -> bool
  val test_pb : tactic -> string * goal list -> bool
  
end
