signature ramsey =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  val ramsey_score : prog -> int * IntInf.int
  
  val enum_shapel_klevel : int * int * int -> (int * int -> bool) -> 
    ((int * int) list * IntInf.int) option
  val enum_shapel_p : int * int * int -> prog -> 
    ((int * int) list * IntInf.int) option
  
  val enum_shapel_free : 
    int -> (int * int -> bool) -> (int * int) list * IntInf.int
  
  
  
  
end
