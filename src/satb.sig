signature satb =
sig
  
  include Abbrev
  type mat = int Array2.array
  
  (* syntax *)
  val E : term
  val X : int -> term
  val Xnum : term -> int
  val hvarij : (int * int) -> term
  val hvar : int -> term
  val hlit : (int * int) -> term
  val is_lit : term -> bool
  val noclique : int -> int * bool -> term
  val clausev_of_thm : thm -> int vector
  
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
  
  (* flags and memories *)
  val final_thm : thm ref
  val thmv_glob : thm vector ref
  val thm_of_graph : mat -> thm
  val proof_flag : bool ref
  val iso_flag : bool ref
  val isod_glob : (IntInf.int, thm * int list) Redblackmap.dict ref
  val allsat_flag : bool ref
  
  (* solver *)
  val sat_solver : int -> int * int -> mat list
  val sat_solver_edgecl : ((int * int) * int) list -> int -> int * int -> mat list
  
  (* post-processing *)
  val ELIM_COND : int -> thm -> thm
  
end
