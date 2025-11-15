signature qlang = sig
    
  type prog = kernel.prog
  type formula = kernel.prog
  datatype obje = Thm of formula list * int | Term of formula
  type obj = obje list
  
  exception Error
  exception Proof
  
  val mk_thm : formula list -> obj
  val dest_thm : obj -> formula list
  
  (* axioms *)
  val refl_ax : obj
  val sym_ax : obj
  val peano1 : obj
  val peano2 : obj
  
  (* rules *)
  val paramodulate_obj : obj -> obj -> obj (* rw *)
  val resolve_obj : obj -> obj -> obj (* mp *)
  val factor_obj : obj -> obj (* fact *)

  (* programming primitives *)
  val varx : obj * obj -> obj
  val vary : obj * obj -> obj
  val cond : obj -> (unit -> obj) -> (unit -> obj) -> obj 
  val while2 : (obj * obj -> obj) -> (obj * obj -> obj) -> obj -> obj -> obj
  
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
  val is_zero : obj -> obj
  val is_suc : obj -> obj
  val is_add : obj -> obj
  val dest : obj -> obj
  

end
