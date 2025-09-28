signature qprove = sig

  type prog = kernel.prog
  type branch = {have : prog Redblackset.set, pending : prog list}
  
  val or : prog -> prog -> prog
  val var : int -> prog
  val neg : prog -> prog
  val forall : prog -> prog -> prog
  
  val dropf_glob : (branch -> bool) ref
  val prove : prog list -> prog -> bool
  val refute : prog list -> bool
  
end
