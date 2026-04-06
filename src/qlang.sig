signature qlang = sig
  
  type formula = qsyntax.formula
  type goal = formula list * formula
  type tactic = goal list -> goal list
  type proof = string list
  type proofe = proof * (int * int)
  type entry = goal list * proofe list

  (* goal utilities *)
  val goal_size : goal -> int
  val goall_size : goal list -> int
  val goal_compare : goal * goal -> order
  val goall_compare : goal list * goal list -> order
  val goal_to_sexp : goal -> sexp.sexp
  val sexp_to_goal : sexp.sexp -> goal
  val goall_to_sexp : goal list -> sexp.sexp
  val sexp_to_goall : sexp.sexp -> goal list
  
  (* parsing problems *)
  val get_problems : unit -> (string * goal list) list
  val changed : 'a list -> int -> unit
  
  (* misc *)
  val s1 : 'a list -> 'a
  val s2 : 'a list -> 'a
  val s3 : 'a list -> 'a
  val s4 : 'a list -> 'a
  val s5 : 'a list -> 'a
  val arg : formula -> formula list
  val repeat : (''a -> ''a) -> ''a -> ''a
  val argf : int -> (formula -> formula) -> formula -> formula 
  val depends_on : qsyntax.id -> qsyntax.formula -> bool
  val sample_distrib : ('a * real) list -> ('a * real)

  (* replace *)
  val replace_atl : (formula -> formula) -> formula -> formula
  val replace_atlh : (formula -> formula) -> formula -> formula
  val replace_bu : (formula -> formula) -> formula -> formula
  val replace_id : qsyntax.id * qsyntax.id -> formula -> formula
  val replace : formula * formula -> formula -> formula
  val replace_asm : int -> tactic
  val replace_asm_sym : int -> tactic
  
  (* unfold *)
  val unfold : formula -> formula
  val unfoldh : formula -> formula
  val unfold_num : formula -> formula
 
  (* normalize *)
  val formula_to_poly : formula -> (formula list * int) list
  val poly_to_formula : (formula list * int) list -> formula
  val norm_poly : formula -> formula
  val simp : formula -> formula
  
  (* generalize *)
  val decouple1 : tactic
  val decouple2 : tactic
  val gen_idloop : tactic
  val swap_var : int -> tactic
  
  
  (* pattern_match *)
  val fold_one : int -> formula -> formula
  val constant_loop2h : formula -> formula
  val linear_loop2h : formula -> formula
  val pow_mult : formula -> formula
  val loop2h_to_loop : formula -> formula 
  val foldrh : tactic  
  val foldlh : tactic  
    
  (* induction tactics *)
  val induct : tactic
  val induct2 : tactic
  val induct_para : tactic

  (* goal tactics *)
  val auto : tactic
  val imitate : tactic
  val refl : tactic
  
  (* assumption tactics *)
  val drop_asm : tactic
  val tl_asm : tactic
  val apply_asmk : int -> (formula -> formula) -> tactic
  val addzero_asmk_left : int -> tactic
   
  (* conjectures *)
  val conjecture : formula option -> tactic
  val cj2 : tactic
  val cj3 : tactic 
   
  (* goal management *)
  val apply_tac : tactic -> tactic
  val pg : goal -> unit 
  val pgl : goal list -> unit
  val stack : goal list list ref 
  val e : tactic -> unit
  val back : unit -> unit
  val init_proof : goal list -> unit
  val init_pb : (string * goal list) list -> unit
  val apply_concl : (formula -> formula) -> tactic
  val apply_asm : (formula -> formula) -> tactic
  val apply_all : (formula -> formula) -> tactic
  val ac : (formula -> formula) -> tactic
  val aa : (formula -> formula) -> tactic
  val aall : (formula -> formula) -> tactic
  val >> : goal list * tactic -> goal list
  
  val is_proof: tactic -> goal list -> bool
  val test_pb : tactic -> string * goal list -> bool
  
  (* proof search *)
  val uniform_policy : 'a list -> goal list -> ('a * real) list
  val search : int -> (goal list -> ((string * tactic) * real) list) -> 
    goal list -> unit
  val retry : real -> (goal list -> ((string * tactic) * real) list) ->
    goal list -> unit
  val record : (string * tactic) list -> 
    goal list -> unit

  (* storing best proofs *)  
  val proofd : (goal list, proofe list) Redblackmap.dict ref
  val to_disk : string -> entry list -> unit
  val from_disk : string -> entry list
  val init_proofd : unit -> unit
  val update_proofd : entry -> unit
  val get_proofd : unit -> entry list
  
  
  
  

end
