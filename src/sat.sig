signature sat =
sig

  type mat = int Array2.array
  
  (* vector with constant time deletion *)
  val dlv_fromlist : 'a -> 'a list -> ((int ref * int ref) * 'a) vector
  val dlv_del : int -> ((int ref * int ref) * 'a) vector -> unit -> unit
  val dlv_app : ('a -> 'b) -> (('c * int ref) * 'a) vector -> unit
  val dlv_null : (('a * int ref) * 'b) vector -> bool
  
  (* conversion between edges and variables *)
  val search_order_undirected : int -> (int * int) list
  val var_to_edge : int -> (int * int)
  val edge_to_var : (int * int) -> int
  
  (* clauses *)
  val ramsey_clauses : int -> int * int -> (int * int) list list

  (* sat *)
  val allsat_flag : bool ref
  val sat_solver : int -> int * int -> mat list
  val sat_solver_edgecl : mat -> int -> int * int -> mat list
  
end
