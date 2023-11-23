signature exec_prim =
sig

val checktimer : unit -> unit

val tzero : unit -> IntInf.int
val tone : unit -> IntInf.int
val ttwo : unit -> IntInf.int
val taddi : IntInf.int -> IntInf.int -> IntInf.int
val tdiff : IntInf.int -> IntInf.int -> IntInf.int
val tmult : IntInf.int -> IntInf.int -> IntInf.int
val tdivi : IntInf.int -> IntInf.int -> IntInf.int
val tmodu : IntInf.int -> IntInf.int -> IntInf.int
val tleq0 : IntInf.int -> bool

type rat = IntInf.int * IntInf.int
val treduce : rat -> rat

val rzero : unit -> rat
val rone : unit -> rat
val rtwo : unit -> rat
val raddi : rat -> rat -> rat
val rdiff : rat -> rat -> rat
val rmult : rat -> rat -> rat
val rdivr : rat -> rat -> rat
val rdivi : rat -> rat -> rat
val rmodu : rat -> rat -> rat
val rgcd : rat -> rat -> rat
val rfloor : rat -> rat
val rnumer : rat -> rat
val rdenom : rat -> rat
val rleq0 : rat -> bool

type complex = rat * rat
val czero : unit -> complex
val cone : unit -> complex
val ctwo : unit -> complex
val caddi : complex -> complex -> complex
val cdiff : complex -> complex -> complex
val cmult : complex -> complex -> complex
val cdivr : complex -> complex -> complex
val cdivi : complex -> complex -> complex
val cmodu : complex -> complex -> complex

val cleq0 : complex -> bool


(* tree of numbers ('a could be IntInf.int, rat or complex) *)
datatype 'a ctree = 
  CLeaf of 'a | 
  CNode1 of 'a * 'a ctree | 
  CNode2 of 'a * 'a ctree * 'a ctree
val pop : 'a ctree -> 'a ctree
val push : 'a ctree -> 'a ctree -> 'a ctree

(* extra primitives *)
val popr : 'a ctree -> 'a ctree
val push2 : 'a ctree -> 'a ctree -> 'a ctree -> 'a ctree
(* val cdivr : complex -> complex -> complex *)
val cfloor : complex -> complex
val cnumer : complex -> complex
val cdenom : complex -> complex
val cgcd : complex -> complex -> complex
val cimag : unit -> complex
val crealpart : complex -> complex
val cimagpart : complex -> complex

(* 
not subject to the timer but convenient to define loops 
other instructions in the loops are much more expensive
and this is to be backward compatible with previous time measurement
*)
val mk_ctree : 'a -> 'a ctree
val root : 'a ctree -> 'a
val ctincr : complex ctree -> complex ctree
val ctzero : complex ctree
val ctone : complex ctree
val ctmone : complex ctree
val mk_bound : complex ctree -> int
val mk_return : complex ctree -> IntInf.int

end
