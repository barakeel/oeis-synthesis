signature check =
sig

  type ('a,'b) dict = ('a,'b) Redblackmap.dict
  type anum = bloom.anum
  
  val update_wind_one :  
    (anum, kernel.prog) dict ref -> anum * kernel.prog -> unit
  val update_altwind_one : 
    (anum * anum, kernel.prog) dict ref -> anum * kernel.prog -> unit

  val check : kernel.prog list -> 
    (anum * kernel.prog) list * (anum * kernel.prog) list

end
