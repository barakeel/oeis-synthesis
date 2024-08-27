signature arcagi =
sig
  
  include Abbrev
  
  type mat = int Array2.array
  type ex = (mat * mat) list * (mat * mat)

            
  val read_ex : string -> (mat * mat) list * (mat * mat) list
  val trainex_glob : ex vector ref
  val read_trainex : unit -> unit

  val match_output : (int * int -> int) -> int Array2.array -> bool * int
  val compute_output : (int * int -> int) -> int Array2.array
  
  val get_colo : int Array2.array list -> int list
  val mk_fun : ex -> kernel.prog -> ((int * int) -> int)
  
  val best_glob : (kernel.prog * bool * int) list ref
  val ex_glob : ex ref
  val score : ex -> kernel.prog -> (bool * int) option
          
  
end
