structure execarb :> execarb =
struct

open HolKernel boolLib aiLib kernel bloom;
val ERR = mk_HOL_ERR "execarb";
type prog = kernel.prog

(* -------------------------------------------------------------------------
   Instructions
   ------------------------------------------------------------------------- *)

local open Arbint in

val aits = toString

(* wrappers *)
fun mk_nullf opf fl = case fl of
   [] => (fn x => opf x)
  | _ => raise ERR "mk_nullf" ""

fun mk_unf opf fl = case fl of
   [f1,f2] => (fn x => opf (f1 x))
  | _ => raise ERR "mk_unf" ""

fun mk_binf opf fl = case fl of
   [f1,f2] => (fn x => opf (f1 x, f2 x))
  | _ => raise ERR "mk_binf" ""

fun mk_ternf opf fl = case fl of
   [f1,f2,f3] => (fn x => opf (f1 x, f2 x, f3 x))
  | _ => raise ERR "mk_ternf" ""

fun mk_binf1 opf fl = case fl of
   [f1,f2] => (fn x => opf (f1, f2 x))
  | _ => raise ERR "mk_binf1" ""

fun mk_ternf1 opf fl = case fl of
   [f1,f2,f3] => (fn x => opf (f1, f2 x, f3 x))
  | _ => raise ERR "mk_ternf1" ""

fun mk_quintf2 opf fl = case fl of
   [f1,f2,f3,f4,f5] => 
   (fn x => opf (f1, f2, f3 x, f4 x, f5 x))
  | _ => raise ERR "mk_quintf2" ""

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

val a256 = fromInt 256
fun compr_f_aux x f n0 n =
  if x > (n0+one)*(n0+one)*a256 then raise Div
  else if f (x,zero) <= zero then 
   (if n0 >= n then x else compr_f_aux (x+one) f (n0+one) n)
  else compr_f_aux (x+one) f n0 n
fun compr_f_aux2 (f,n) = compr_f_aux zero f zero n
val compr_f = mk_binf1 compr_f_aux2
fun loop2_f_aux f1 f2 n x1 x2 = 
  if n <= zero
  then x1 
  else loop2_f_aux f1 f2 (n-one) (f1 (x1,x2)) (f2 (x1,x2))

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

fun mk_execarb (Ins (id,pl)) =
  Vector.sub (base_execv,id) (map mk_execarb pl)

fun find_wins p = tcover (mk_execarb p)

end (* struct *)

(* 
load "bloom"; load "execarb";  
open bloom execarb kernel;
val p = Ins (10,[]);
val f = ;
val winl =  f;
*)


