signature rconfig =
sig

  val real_time : real
  val abstract_time : int
  val memory : int
  val ncore : int
  
  (* logging *)
  val disable_log : bool ref
  val store_log : bool ref
  val logfile : string ref 
  val log : string -> unit
  
end
