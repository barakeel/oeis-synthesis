signature sat =
sig

  type mat = int Array2.array
  (* clauses *)
  val all_clauses : int -> mat * mat -> (int * int) list list
  val sbl_clauses : int -> (int * int) list list
  val all_clauses3 : int -> int * int -> mat -> ((int * int) * int) list list
  
  (* sat *)
  val sat_solver : int -> mat * mat -> bool
  
  (* I/O *)
  val write_satpb : string -> int * (int * int) list list -> unit
  
  
  
end
