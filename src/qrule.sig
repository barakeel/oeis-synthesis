signature qrule = sig

  type formula = qsyntax.formula
  type clause = formula list
  
  (* unification (substitution is a side effect) *)
  val unify : formula * formula -> bool 
  
  (* explicit rules *)
  val paramodulate : clause -> formula * formula -> clause * int -> clause option
  val resolve : clause -> (clause * int) -> clause option
  val factor : (clause * int) -> clause option
  
  (* automatic rules *)
  val factor_set : clause -> clause
  val remove_conflict : clause -> clause
  val remove_diseq : clause -> clause
  
end

