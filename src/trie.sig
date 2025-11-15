signature trie = sig

datatype trie = 
  Trie of int ref * int ref * (int,trie) Redblackmap.dict ref;
  
val taddl : trie -> int list -> unit
val treml : trie -> int list -> unit
val tnew : int list list -> trie
val tlist : int -> trie -> (int list * int) list

val tmax : trie -> int list * int
val name_def : trie -> int list * int -> int list -> int list
val mk_def : trie -> int -> int list list -> (int list * int) list * int list list

end
