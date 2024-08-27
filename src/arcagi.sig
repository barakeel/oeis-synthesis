signature arcagi =
sig
  
  include Abbrev
  
  type mat = int Array2.array
  type ex = (mat * mat) list * (mat * mat) list
  
  val trainex_glob : ex vector ref
  val ex_glob : ex ref
  val exi_glob : int ref 
  
  val read_ex : string -> ex
  val read_trainex : unit -> unit
  val compute_output : (int * int -> int) -> int Array2.array
  val score : ex -> kernel.prog -> (bool * int) option
          
  
end
