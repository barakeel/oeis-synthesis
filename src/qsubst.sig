signature qsubst = sig

  type prog = kernel.prog
  
  val inst_match : prog * prog * prog -> prog
  val rewrite_match : prog * prog -> prog
  val mp_match : prog * prog -> prog
  
end

