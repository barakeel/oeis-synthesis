signature qlang = sig
  
  type formula = qsyntax.formula
  datatype obje = Thm of formula list * int | Term of formula
  type obj = obje list
  type eq = formula * formula
  
  exception Error
  exception Proof
  
  val mk_thmobj : formula list -> obj
  val dest_thmobj : obj -> formula list
  val mk_thm : formula list -> obje
  val dest_thm : obje -> formula list
  
  (* messages *)
  val hfobj : obj -> string
  val see : obj -> unit
  
  val x_flag : bool ref (* tells if we know if x0 is nonnegative *)
  
  val replace_atl : (formula -> formula) -> formula -> formula
  
  val unfold : formula -> formula
  val unfold_num : formula -> formula
  val decouple : formula -> formula

  val induct_help :  qsyntax.formula * qsyntax.formula ->
    (qsyntax.formula * qsyntax.formula) list ->
    (qsyntax.formula * qsyntax.formula) list *
    (qsyntax.formula * qsyntax.formula) list *
    (qsyntax.formula * qsyntax.formula) list
  
  val replace_id : qsyntax.id * qsyntax.id -> qsyntax.formula -> qsyntax.formula
  val equality_help : eq -> eq
  
  (* axioms *)
  (*
  val refl_ax : obj
  val sym_ax : obj
  val suc_inj : obj
  val add_zero : obj
  val add_suc : obj
  val mult_zero : obj
  val mult_suc : obj
  val distrib : obj
  val add_com : obj
  val mult_com : obj
  val divdiv : obj
  val mult_one : obj
  *)
  
  (* rules *)
  val next_obj : obj -> obj
  val paramodulate_obj : obj -> obj -> obj (* rw *)
  val resolve_obj : obj -> obj -> obj (* mp *)
  val factor_obj : obj -> obj (* fact *)
  val induct_obj : (obj * obj -> obj) -> obj -> obj
  val induct_obji : obj -> (obj * obj)
  
  (* programming primitives *)
  val varx : obj * obj -> obj
  val vary : obj * obj -> obj
  val cond : obj -> (unit -> obj) -> (unit -> obj) -> obj 
  val while2 : (obj * obj -> obj) -> (obj * obj -> obj) -> obj -> obj -> obj
  val repeat : (''a -> ''a) -> ''a -> ''a
  
  (* list *)
  val hd_obj : obj -> obj
  val tl_obj : obj -> obj
  val push_obj : obj -> obj -> obj
  val null_obj : obj
  
  (* test and term *)
  val eq_obj : obj -> obj -> obj
  val same_id : obj -> obj -> obj
  val is_var : obj -> obj
  val is_not : obj -> obj
  val is_eq : obj -> obj
  val is_add : obj -> obj
  val dest : obj -> obj
  
  (* normalizations *)
  val formula_to_poly : formula -> (formula list * int) list
  val poly_to_formula : (formula list * int) list -> formula
  val norm_poly : formula -> formula
  val norm_poly_obj : obj -> obj
  
  (* generalizations *)
  val gen_idloop : formula -> formula
  
  (* pattern match *)
  val constant_loop2h : formula -> formula
  
  
  (* parsing problems *)
  val conjecture_of : string -> string -> string

  (* *)
  val induct_case_both_loop2 : eq -> eq * (eq * eq) * (eq * eq)
  
  val refl_eq : eq -> eq
  val eval_eq : eq -> eq
  val hf_eq : eq -> unit
  val pairmap : (formula -> formula) -> eq -> eq
  val pairfst : (formula -> formula) -> eq -> eq
  
  (* helpers *)
  val replace : eq -> formula -> formula
  
  (* chooses a subterm of a formula *)
  val s1 : 'a list -> 'a
  val s2 : 'a list -> 'a
  val s3 : 'a list -> 'a
  val s4 : 'a list -> 'a
  val s5 : 'a list -> 'a
  val arg : formula -> formula list

  (* goal based primitives *)
  type goal = formula list * formula
  type tactic = goal list -> goal list
  
  val apply_concl : (formula -> formula) -> tactic
  val apply_asm : (formula -> formula) -> tactic
  val apply_all : (formula -> formula) -> tactic
  val get_problems : unit -> (string * goal list) list
  val pg : goal -> unit 
  val pgl : goal list -> unit
  val induct : tactic
  val induct2 : tactic
  val induct2_2 : tactic
  val refl : tactic (* could be automatic *)
  val replace_asm : int -> tactic
  val drop_asm : tactic
  val auto : tactic
  
  
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
