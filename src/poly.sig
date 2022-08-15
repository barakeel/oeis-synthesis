signature poly =
sig

  datatype poly = Poly of ((int * poly list) list * IntInf.int) list
  val poly_compare : poly * poly -> order
  val normalize : kernel.prog -> poly  
  
end
