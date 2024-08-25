signature ramsey =
sig
  
  include Abbrev
  
  type prog = kernel.prog
    
  (* boolean square symmetric matrices *)
  val mat_sub : bool Array2.array * int * int -> bool
  val mat_tabulate : int * (int * int -> bool) -> bool Array2.array
  val mat_size : bool Array2.array -> int
  val print_mat : bool Array2.array -> unit
  val mat_bti : bool Array2.array -> int Array2.array
  val mat_itb : int Array2.array -> bool Array2.array
  
  (* cliques *)
  val exist_clique : int -> (int * int -> bool) -> int list -> bool
  val max_clique : (int * int -> bool) -> int list -> int
  val max_clique_both : int * (int * int -> bool) -> int
  val max_clique_both0 : int * (int * int -> bool) -> int
  val all_clique : int -> (int * int -> bool) -> int list -> int list list
  
  (* arithmetic *)
  val primes_leq : int -> int list
  val create_is_square_mod : int -> (int * int) -> bool
  val derive : int list -> int list
  
  (* incremental checking of clique *)
  val loop_minclique : (int * int -> bool) -> int * int -> 
    (int * IntInf.int) * ((int * int) list * (int * int) list)
  
  (* reinforment learning *)
  val ramsey_score : prog -> (int * IntInf.int) option
  val execspec : (unit, prog, int * (int list * int list)) smlParallel.extspec
  val no_hash : bool ref
  val parallel_exec : string -> unit
  val skip_test : bool ref
  
end
