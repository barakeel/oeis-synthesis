signature hanabi =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  type exec = int list * int list -> int list
  type board = 
  {
  clue : int ref, 
  bomb: int ref, 
  score: int ref, 
  turn: int ref,
  hand1 : ((int*bool)*(int*bool)) list ref,
  hand2 : ((int*bool)*(int*bool)) list ref,
  deck : (int * int) list ref, 
  deckn : int ref,
  firework : int Array.array,
  discard : int Array2.array
  };
  
  val mk_exec: prog -> exec
  val cardl : (int * int) list
  val deckl_glob : (int * int) list list
  val play_game : bool -> prog -> (int * int) list -> (int * int list)
  val hanabi_score : prog -> (int * IntInf.int)
  val write_deckl : string -> (int * int) list list -> unit
  val read_deckl : string -> (int * int) list list
  
end
