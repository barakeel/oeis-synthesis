structure exec_pow :> exec_pow =
struct

open HolKernel boolLib aiLib kernel bloom smlParallel
val ERR = mk_HOL_ERR "exec_pow"
type prog = kernel.prog
type exec = IntInf.int -> IntInf.int

(* -------------------------------------------------------------------------
   Time limit
   ------------------------------------------------------------------------- *)

local open IntInf in
  val azero = fromInt 0
  val aone = fromInt 1
  val atwo = fromInt 2
  val aten = fromInt 10  
  fun aincr x = x + aone
  fun adecr x = x - aone
  fun arb_pow a b = if b <= azero then aone else a * arb_pow a (b-aone)
  fun pow2 b = arb_pow atwo (fromInt b)
  val maxarb = arb_pow (fromInt 10) (fromInt maxintsize) (* 4.685 * 10 ^ 284 *)
  val minarb = ~maxarb
  val maxint = fromInt (valOf (Int.maxInt))
  val minint = fromInt (valOf (Int.minInt))
  fun large_arb x = x > maxarb orelse x < minarb
  fun large_int x = x > maxint orelse x < minint
end

fun cost costn x = 
  if large_arb x then raise Overflow else
  if large_int x then IntInf.log2 (IntInf.abs x) else costn

fun checktimer costn y =
  let val _ = abstimer := !abstimer + cost costn y in
    if !abstimer > !timelimit then raise ProgTimeout else y
  end
  
fun cost_pow x = 
  if large_arb x then raise Overflow else 
  if IntInf.abs x < aten then 5 else IntInf.log2 (IntInf.abs x)
  
fun checktimer_pow y =
  let val _ = abstimer := !abstimer + cost_pow y in
    if !abstimer > !timelimit then raise ProgTimeout else y
  end  
  
(* -------------------------------------------------------------------------
   Time limit wrappers
   ------------------------------------------------------------------------- *)

fun mk_nullf opf fl = case fl of
   [] => (fn x => checktimer 1 (opf x))
  | _ => raise ERR "mk_nullf" ""

fun mk_unf opf fl = case fl of
   [f1] => (fn x => checktimer 1 (opf (f1 x)))
  | _ => raise ERR "mk_unf" ""

fun mk_binf costn opf fl = 
  case fl of
   [f1,f2] => (fn x => checktimer costn (opf (f1 x, f2 x)))
  | _ => raise ERR "mk_binf" ""

fun mk_binf_pow opf fl = 
  case fl of
   [f1,f2] => (fn x => checktimer_pow (opf (f1 x, f2 x)))
  | _ => raise ERR "mk_binf_pow" ""

fun cond_f fl = case fl of
   [f1,f2,f3] => 
      (fn x =>
       let 
         val y = if f1 x <= azero then f2 x else f3 x
         val _ = abstimer := !abstimer + 1  
       in
         if !abstimer > !timelimit then raise ProgTimeout else y
       end)
  | _ => raise ERR "mk_condf" ""
  
(* -------------------------------------------------------------------------
   Basic intructions
   ------------------------------------------------------------------------- *)
 
val zero_f = mk_nullf (fn _ => azero)
val one_f = mk_nullf (fn _ => aone)
val two_f = mk_nullf (fn _ => atwo)
val ten_f = mk_nullf (fn _ => aten)
val x_f = mk_nullf (fn x => x)
val addi_f = mk_binf 1 (op +)
val diff_f = mk_binf 1 (op -)
val mult_f = mk_binf 1 (op *)
val divi_f = mk_binf 5 (op div)
val modu_f = mk_binf 5 (op mod)

val maxintsize3 = 3 * maxintsize

fun pow (a,b) = 
  let val b' = IntInf.toInt b in
    if b = azero then aone else
    if a = azero then azero else 
    if IntInf.log2 (IntInf.abs a) * b' > maxintsize3 then raise ProgTimeout
    else IntInf.pow (a,b')
  end

val pow_f = mk_binf_pow pow

(* -------------------------------------------------------------------------
   Execute a program
   ------------------------------------------------------------------------- *)

val execv = Vector.fromList 
  [zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,cond_f,pow_f,x_f,ten_f]

fun mk_exec_move id fl = Vector.sub (execv,id) fl
  
fun mk_exec (p as (Ins (id,pl))) = 
  let val fl = map mk_exec pl in mk_exec_move id fl end
  

end (* struct *)
