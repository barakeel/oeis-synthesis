signature match =
sig

  include Abbrev
  type seq = kernel.seq
  type prog = kernel.prog
  type pf = prog * (IntInf.int -> IntInf.int option)
  
  val enum_backp : real -> prog list
  val back_image_pl : seq -> prog list -> (seq * prog) list
  val enum_repairp : real -> prog list
  val repair_cache_flag : bool ref
  val create_f : prog -> IntInf.int -> IntInf.int option
  
  val find_repair : seq list -> prog list -> seq -> (seq * prog) list
  val collect_inverse : pf list -> pf list -> (pf * pf) list
  
  val human_of_inv : (kernel.seq * (int * (kernel.prog * kernel.prog))) -> string 
  val write_invl : string ->
    (kernel.seq * (int * (kernel.prog * kernel.prog))) list -> unit
  val read_invl : string ->
    (kernel.seq * (int * (kernel.prog * kernel.prog))) list
  val inverse_an_unit : (pf * pf) list -> int * IntInf.int list -> unit
  
  val write_pfpfl : string -> (pf * pf) list -> unit
  val read_pfpfl : string -> (pf * pf) list
  
end
