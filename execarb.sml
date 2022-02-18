structure execarb :> execarb =
struct

open HolKernel boolLib aiLib kernel bloom;
val ERR = mk_HOL_ERR "execarb";

val arbentryl = List.tabulate (101,fn x => (Arbint.fromInt x,Arbint.zero))

(* -------------------------------------------------------------------------
   Instructions
   ------------------------------------------------------------------------- *)

val aits = Arbint.toString
val (aol,aod) = import_arbseq ()
fun find_arbmax_aux a m = case m of
    [] => a
  | a1 :: m1 => Arbint.max (a, find_arbmax_aux a1 m1)

fun find_arbmax l = case l of
   [] => raise ERR "find_arbmax" ""
 | a :: m => find_arbmax_aux a m

val maxarb = find_arbmax (List.concat (dkeys aod))

(* time limit per instruction *)
val arbmaxinput = ref 16
fun timescale () = !arbmaxinput
fun timescale2 () = int_pow (timescale ()) 2
fun timescale4 () = int_pow (timescale ()) 4 + 1

exception ArbOverflow;

local open Arbint in

fun protect r = if r > maxarb then raise ArbOverflow else r

val arb_zero_f = (fn _ => zero)
val arb_one_f = (fn _ => one)
val arb_two_f = (fn _ => two)
val arb_var_f = (fn (a:Arbint.int,b:Arbint.int) => a)
val arb_ind_f = (fn (a:Arbint.int,b:Arbint.int) => b)

(* first-order *)
fun arb_addi_f (a,b) = protect (a + b)
fun arb_diff_f (a,b) = protect (a - b)
fun arb_mult_f (a,b) = protect (a * b)
fun arb_divi_f (a,b) = protect (a div b)
fun arb_modu_f (a,b) = protect (a mod b)
fun arb_cond_f (a,b,c) = protect (if a <= zero then b else c)

(* higher-order *)
fun arb_loop_f_aux i f n x = 
   (
   incr counter;
   if FixedInt.> (!counter,timescale4 ()) then raise Div
   else if n <= zero then x 
   else arb_loop_f_aux (i+one) f (n-one) (f (x,i))
   )

fun arb_loop_f f (n,x) = arb_loop_f_aux one f n x

fun arb_compr_f_aux x f n0 n =
   (
   if x > (n0+one)*(n0+one)*(Arbint.fromInt (timescale2 ())) then raise Div else ();
   incr counter;
   if FixedInt.> (!counter,timescale4 ()) then raise Div
   else if f (x,zero) <= zero then 
     (if n0 >= n then x else arb_compr_f_aux (x+one) f (n0+one) n)
   else arb_compr_f_aux (x+one) f n0 n
   )

fun arb_compr_f f n = arb_compr_f_aux zero f zero n

end

(* regroup by arity *)
val arb_nullaryl =
 [(zero_id,arb_zero_f),(one_id,arb_one_f),(two_id,arb_two_f),
  (var_id,arb_var_f),(ind_id,arb_ind_f)]

fun find_arb_nullaryf id = assoc id arb_nullaryl
val arb_nullaryv = Vector.tabulate (maxoper, fn i => 
  if can find_nullaryf i then find_arb_nullaryf i else arb_zero_f);

val arb_binaryl = 
  [(addi_id,arb_addi_f),(diff_id,arb_diff_f),(mult_id,arb_mult_f),
   (divi_id,arb_divi_f),(modu_id,arb_modu_f)]
fun find_arb_binaryf id = assoc id arb_binaryl
val arb_binaryv = Vector.tabulate (maxoper, fn i => 
  if can find_binaryf i then find_arb_binaryf i else arb_addi_f);

(* -------------------------------------------------------------------------
   Execute a program on some input
   ------------------------------------------------------------------------- *)

fun compose1 f f1 x = f (f1 x)
fun compose2 f f1 f2 x = f (f1 x, f2 x)
fun compose3 f f1 f2 f3 x = f (f1 x, f2 x, f3 x)

fun arb_mk_exec_aux prog = case prog of
    Ins (id,[]) => Vector.sub (arb_nullaryv,id) 
  | Ins (12,[p1,p2]) =>
    compose1 (arb_compr_f (arb_mk_exec_aux p1)) (arb_mk_exec_aux p2)
  | Ins (id,[p1,p2]) => 
    compose2 (Vector.sub (arb_binaryv,id)) 
       (arb_mk_exec_aux p1) (arb_mk_exec_aux p2)
  | Ins (8,[p1,p2,p3]) => 
    compose3 arb_cond_f (arb_mk_exec_aux p1) 
       (arb_mk_exec_aux p2) (arb_mk_exec_aux p3)
  | Ins (9,[p1,p2,p3]) =>
    compose2 (arb_loop_f (arb_mk_exec_aux p1)) 
       (arb_mk_exec_aux p2) (arb_mk_exec_aux p3)
  | _ => raise ERR "arb_mk_exec_aux" ""  

fun arb_mk_exec p =
  let val exec = start (arb_mk_exec_aux p) in
    (fn x => (exec x handle Div => Arbint.fromInt error 
                          | ArbOverflow => Arbint.fromInt error))
  end 

fun arb_seq_of_prog n p =
  let 
    val _ = arbmaxinput := n
    val f = arb_mk_exec p 
  in 
    map f (first_n n arbentryl) 
  end
  

fun mk_aodnv n =
  let
    val ln = map (first_n n) (dkeys aod)
    val aodvref = Vector.tabulate (n + 1, 
      fn _ => ref (eempty (list_compare Arbint.compare)))
    fun f seq = 
      let val aodref = Vector.sub (aodvref,length seq) in
        aodref := eadd seq (!aodref)
      end  
    val _ = app f ln
    val r = Vector.map ! aodvref
  in
    r
  end

end (* struct *)

(* 
load "mcts"; load "execarb";  open aiLib mcts execarb;
expname := "run112";
val pl = elist (read_sold 0);

fun arb_update_wind wind n aodv seq =
  let
    val seql = List.tabulate (n + 1, fn i => 
      let val subseq = first_n i seq in
        if emem subseq (Vector.sub (aodv,i))
        then wind := eadd subseq (!wind)
        else ()
      end)
  in
    ()
  end ;

fun number_sol n = 
  let
    val aod16v = mk_aodnv n;
    val wind = ref (eempty (list_compare Arbint.compare));
    val seql = map (arb_seq_of_prog n) pl;
  in
    app (arb_update_wind wind n aod16v) seql;
    elength (!wind)
  end;

List.tabulate (17, fn x => number_sol (16 + x));





*)



