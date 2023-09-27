signature satenc =
sig

  type mat = int Array2.array

  
  val atmostk : int -> int -> (string * bool) list list
  val atleastk : int -> int -> (string * bool) list list
  val atmostk_named : int -> string list -> string -> (string * bool) list list
  val atleastk_named : int -> string list -> string -> (string * bool) list list
  
  val ramsey_clauses : int -> (int * int) -> (string * bool) list list
  
  
  
  val read_mapping : string -> ((int * int) * (string, int) Redblackmap.dict)
  val write_assignl : string -> ((int * int) * (string, int) Redblackmap.dict) -> 
    string -> mat * mat -> unit
  
  
  val write_pb : string -> (string * bool) list list -> unit
  val write_pb_10_14 : string -> unit
  val write_r45_pb : string -> unit
  val write_r45_pb_wdeg : int -> int * int -> string -> unit
end
