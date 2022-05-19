structure execarb :> execarb =
struct

open HolKernel boolLib aiLib kernel bloom;
val ERR = mk_HOL_ERR "execarb";
type prog = kernel.prog

(* -------------------------------------------------------------------------
   Time limit
   ------------------------------------------------------------------------- *)

local open Arbint in
  fun arb_pow a b = if b <= zero then one else a * arb_pow a (b-one)
  val maxarb = arb_pow (fromInt 10) (fromInt 285) (* 4.685 * 10 ^ 284 *)
  val minarb = ~maxarb
  val maxint = arb_pow (fromInt 2) (fromInt 64)
  val minint = ~maxint
  fun large_arb x = x > maxarb orelse x < minarb
  fun large_int x = x > maxint orelse x < minint
end 

fun test_aux y = 
  let val t = Time.toReal (Timer.checkRealTimer (!rt_glob)) in
    if t > !timelimit then raise ProgTimeout else ()
  end

val skip_counter = ref 0
val skip_large_counter = ref 0

fun test f x =
  let val y = f x in
    if large_arb y then raise ProgTimeout
    else if large_int y then test_aux y
    else 
      if !skip_counter > 1000 
      then (skip_counter := 0; test_aux y) 
      else incr skip_counter;
    y
  end

(* -------------------------------------------------------------------------
   Instructions
   ------------------------------------------------------------------------- *)
 
fun mk_nullf opf fl = case fl of
   [] => (fn x => (test opf x))
  | _ => raise ERR "mk_nullf" ""

fun mk_unf opf fl = case fl of
   [f1] => (fn x => (test opf (f1 x)))
  | _ => raise ERR "mk_unf" ""

fun mk_binf opf fl = case fl of
   [f1,f2] => (fn x => (test opf (f1 x, f2 x)))
  | _ => raise ERR "mk_binf" ""

fun mk_ternf opf fl = case fl of
   [f1,f2,f3] => (fn x => (test opf (f1 x, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf" ""

fun mk_binf1 opf fl = case fl of
   [f1,f2] => (fn x => (test opf (f1, f2 x)))
  | _ => raise ERR "mk_binf1" ""

fun mk_ternf1 opf fl = case fl of
   [f1,f2,f3] => (fn x => (test opf (f1, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf1" ""

fun mk_quintf2 opf fl = case fl of
   [f1,f2,f3,f4,f5] => 
   (fn x => (test opf (f1, f2, f3 x, f4 x, f5 x)))
  | _ => raise ERR "mk_quintf2" ""


local open Arbint in

val aits = toString
(* first-order *)
val zero_f = mk_nullf (fn _ => zero)
val one_f = mk_nullf (fn _ => one)
val two_f = mk_nullf (fn _ => two)
val x_f = mk_nullf (fn (x,y) => x)
val y_f = mk_nullf (fn (x,y) => y)
val addi_f = mk_binf (op +)
val diff_f = mk_binf (op -)
val mult_f = mk_binf (op *)
val divi_f = mk_binf (op div)
val modu_f = mk_binf (op mod)
fun cond_f_aux (a,b,c) = if a <= zero then b else c
val cond_f = mk_ternf cond_f_aux

(* higher-order *)
fun loop_f_aux i f n x = 
  if n <= zero then x else loop_f_aux (i+one) f (n-one) (f (x,i))
fun loop_f_aux2 (f,n,x) = loop_f_aux one f n x
val loop_f = mk_ternf1 loop_f_aux2
 
fun compr_f_aux x f n0 n =
   if f (x,zero) <= zero then 
   (if n0 >= n then x else compr_f_aux (x+one) f (n0+one) n)
  else compr_f_aux (x+one) f n0 n
fun compr_f_aux2 (f,n) = compr_f_aux zero f zero n
val compr_f = mk_binf1 compr_f_aux2

fun loop2_f_aux f1 f2 n x1 x2 = 
  if n <= zero then x1 else 
  loop2_f_aux f1 f2 (n-one) (f1 (x1,x2)) (f2 (x1,x2))

fun loop2_f_aux f1 f2 n x1 x2 = 
  if n <= zero then x1 else 
  loop2_f_aux f1 f2 (n-one) (f1 (x1,x2)) (f2 (x1,x2))
fun loop2_f_aux2 (f1,f2,n,x1,x2) = loop2_f_aux f1 f2 n x1 x2
val loop2_f = mk_quintf2 loop2_f_aux2

end (* local *)

val base_execl =
  [
  zero_f,
  one_f,
  two_f,
  addi_f,
  diff_f,
  mult_f,
  divi_f,
  modu_f,
  cond_f,
  loop_f,
  x_f,
  y_f,
  compr_f,
  loop2_f
  ]

val base_execv = Vector.fromList base_execl

(* -------------------------------------------------------------------------
   Execute a program on some input
   ------------------------------------------------------------------------- *)

fun mk_execarb (Ins (id,pl)) = Vector.sub (base_execv,id) (map mk_execarb pl)

fun find_wins p =
  (
  skip_counter := 0;
  rt_glob := Timer.startRealTimer (); 
  tcover (mk_execarb p)
  )

fun pcover p target =
  (
  skip_counter := 0;
  rt_glob := Timer.startRealTimer (); 
  fcover (mk_execarb p) target
  )

fun penum p n = 
  let val f = mk_execarb p in
    skip_counter := 0;
    rt_glob := Timer.startRealTimer (); 
    timelimit := 1.0;
    List.tabulate (n,fn i => f (Arbint.fromInt i,Arbint.zero))
  end

end (* struct *)
