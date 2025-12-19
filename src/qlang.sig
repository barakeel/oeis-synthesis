signature qlang = sig
  
  type formula = qsyntax.formula
  datatype obje = Thm of formula list * int | Term of formula
  type obj = obje list
  
  exception Error
  exception Proof
  
  val mk_thmobj : formula list -> obj
  val dest_thmobj : obj -> formula list
  val mk_thm : formula list -> obje
  val dest_thm : obje -> formula list
  
  (* messages *)
  val hfobj : obj -> string
  val see : obj -> unit
  
  (* axioms *)
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
  val repeat : (obj -> obj) -> obj -> obj
  
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
  val eval : formula -> formula

  (* parsing problems *)
  val conjecture_of : string -> string -> string

end
