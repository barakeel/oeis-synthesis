signature enump =
sig
  
  include Abbrev
  type mat = int Array2.array
  
  val create_pard : int -> int * int -> (IntInf.int,thm) Redblackmap.dict
  
  (* creating R theorems (requires computed enum and cover) *)
  val C_SMALLER : int -> int * int -> bool -> thm
  val R_THM : int -> int * int -> thm
  val NEXT_R_THM : int -> int * int -> thm -> thm 
  val INIT_NEXT_R_THM_ONE : int -> int * int -> unit
  val NEXT_R_THM_ONE : int -> int * int -> IntInf.int -> thm
  
  val write_enumscript : int -> int * int -> 
    int * (int * IntInf.int) list -> unit
  val write_enumscripts : int -> int -> int * int -> unit
  
  
end
