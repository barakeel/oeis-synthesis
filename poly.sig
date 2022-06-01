signature poly =
sig

  datatype poly = Poly of ((int * poly list) list * Arbint.int) list
  val poly_compare : poly * poly -> order
  val norm : kernel.prog -> poly  
  
end
