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


type complex = rat * rat
val czero : unit -> complex
val cone : unit -> complex
val ctwo : unit -> complex
val cimag : unit -> complex
val caddi : complex -> complex -> complex
val cdiff : complex -> complex -> complex
val cmult : complex -> complex -> complex
val cdivr : complex -> complex -> complex
val cdivi : complex -> complex -> complex
val cmodu : complex -> complex -> complex
val cgcd : complex -> complex -> complex
val crealpart : complex -> complex
val cimagpart : complex -> complex
val cfloor : complex -> complex
val cnumer : complex -> complex
val cdenom : complex -> complex


end
