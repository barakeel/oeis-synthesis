signature ramseySyntax =
sig
  
  include Abbrev
  type mat = int Array2.array
  
  (* conversion between edges and variables *)
  val search_order_undirected : int -> (int * int) list
  val var_to_edge : int -> (int * int)
  val edge_to_var : (int * int) -> int
  
  (* syntax *)
  val E : term
  val X : int -> term
  val Xnum : term -> int
  val hvarij : (int * int) -> term
  val hvar : int -> term
  val hlit : (int * int) -> term
  val hlit_to_var : term -> int
  val hlit_to_vc : term -> int * int
  val is_lit : term -> bool
  val noclique : int -> int * bool -> term
  val term_of_graph : mat -> term
  val term_of_edgecl : int -> int -> term
 
end
