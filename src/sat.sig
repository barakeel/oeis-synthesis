signature sat =
sig
  
  include Abbrev
  type mat = int Array2.array
  
  (* vector with constant time deletion *)
  val dlv_fromlist : 'a -> 'a list -> ((int ref * int ref) * 'a) vector
  val dlv_del : int -> ((int ref * int ref) * 'a) vector -> unit -> unit
  val dlv_app : ('a -> 'b) -> (('c * int ref) * 'a) vector -> unit
  val dlv_null : (('a * int ref) * 'b) vector -> bool
  
  (* clauses *)
  val ramsey_clauses : int -> int * int -> (int * int) list list
  val ramsey_clauses_bare : int -> int * int -> ((int * int) * int) list list
  
  (* flags and memories *)
  val final_thm : thm ref
  val thmv_glob : thm vector ref
  val thm_of_graph : mat -> thm
  val proof_flag : bool ref
  val iso_flag : bool ref
  val isod_glob : (IntInf.int, thm * int list) Redblackmap.dict ref
  val gthmd_glob : (IntInf.int, thm * int list) Redblackmap.dict ref
  val allsat_flag : bool ref
  val conep_flag : bool ref
  
  (* solver *)
  val sat_solver : int -> int * int -> mat list
  val sat_solver_wisod : int -> int * int -> 
    (IntInf.int, thm * int list) Redblackmap.dict -> mat list
  val sat_solver_edgecl : ((int * int) * int) list -> 
    int -> int * int -> mat list
  
  
  (* preprocessing *)
  val mk_both_cdef : int -> int * int -> thm * thm
  val init_gthmd : (IntInf.int, thm) Redblackmap.dict ->
    (IntInf.int * (IntInf.int * int list) list) list -> unit
  val init_conethmd : (int list, thm) Redblackmap.dict -> 
    (int list * int list list) list -> unit
  

  (* postprocessing *)
  val ELIM_COND : int -> thm -> thm
  val ELIM_COND_GRAPH : mat -> thm -> thm
  val PROVE_HYPL : thm list -> thm -> thm
  val DISCHL : term list -> thm -> thm
  val PROVE_HYP_EQ : thm -> thm -> thm
  val LESS_THAN_NEXT : int -> thm
  
  
  
end
