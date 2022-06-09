signature check =
sig

  type ('a,'b) dict = ('a,'b) Redblackmap.dict
  type anum = bloom.anum
  
  val merge_isol : 
    (anum * kernel.prog) list ->
    (anum * kernel.prog) list
  val merge_partisol : 
    (anum * ((int * real option) * kernel.prog) list) list -> 
    (anum * ((int * real option) * kernel.prog) list) list

  val check : kernel.prog list -> 
    (anum * kernel.prog) list *  
    (anum * ((int * real option) * kernel.prog) list) list

end
