signature enump =
sig
  
  include Abbrev
  type mat = int Array2.array
  
  (* creating R theorems (requires computed enum and cover) *)
  val C_SMALLER : int -> int * int -> bool -> thm
  val R_THM : int -> int * int -> thm
  val NEXT_R_THM : int -> int * int -> thm -> thm 
  
  
  
end
