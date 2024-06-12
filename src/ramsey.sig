signature ramsey =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  
  val cliquetimemax : int ref
  val graphsizemax : int ref
  
  val exist_clique : int -> (int * int -> bool) -> int list -> bool
  val all_clique : int -> (int * int -> bool) -> int list -> int list list
  val exist_clique_mat : int -> int -> bool Array2.array -> bool
  val enum_shapel : int * int -> (int * int -> bool) -> int * IntInf.int
  val double_graph_f : 
    bool Array2.array -> int -> (int * int * int -> bool) -> bool Array2.array
  val ramsey_score : prog -> (int * IntInf.int) option
  
  val test_expo_f : int -> (int * int -> bool) -> int -> int -> int * string
  val test_expo_p : int -> prog -> int -> int -> int * string
  
  val first_clique : (int * int -> bool) -> int -> int list list
  val derive : int list -> int list
  
  val loop_minclique : (int * int -> bool) ->
    int * int -> (int * int) list * (int * int) list


  
end
