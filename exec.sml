structure exec :> exec =
struct

open HolKernel boolLib aiLib kernel bloom
val ERR = mk_HOL_ERR "exec"
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
 
(* deprecated code for compr *)
fun compr_f_aux x f n0 n =
   if f (x,zero) <= zero then 
   (if n0 >= n then x else compr_f_aux (x+one) f (n0+one) n)
  else compr_f_aux (x+one) f n0 n
fun compr_f_aux2 (f,n) = compr_f_aux zero f zero n
val compr_f = mk_binf1 compr_f_aux2

fun compr_f_cache v f2 x = 
  let val input = Arbint.toInt (f2 x) handle Overflow => raise Div in
    if Int.< (input,0) orelse Int.>= (input, Vector.length v) 
    then raise Div 
    else test Vector.sub (v,input)
  end

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
  [zero_f,one_f,two_f,
   addi_f,diff_f,mult_f,divi_f,modu_f,
   cond_f,loop_f,
   x_f,y_f,
   compr_f,loop2_f]

val base_execv = Vector.fromList base_execl

(* -------------------------------------------------------------------------
   Execute a program on some inputs with auto-initialization of compr
   ------------------------------------------------------------------------- *)

fun mk_exec_aux ccache (p as (Ins (id,pl))) = 
  let val fl = map (mk_exec_aux ccache) pl in
    if id = 12 then
      let val v = dfind (hd pl) ccache handle NotFound =>
        raise ERR "mk_exec_aux" (raw_prog p)
      in compr_f_cache v (hd (tl fl)) end 
    else Vector.sub (base_execv,id) fl
  end
  
fun add_ccache ccache p =
  if dmem p (!ccache) then () else
  let
    val _ = init_timer ()
    val f = mk_exec_aux (!ccache) p
    val l = ref []
    fun loop i x =
      if i >= 1000 then () else
      if Arbint.<= (f (x, Arbint.zero), Arbint.zero)
      then (l := x :: !l; incr_timer (); loop (i+1) (Arbint.+ (x,Arbint.one))) 
      else  loop i (Arbint.+ (x,Arbint.one))
    val _ = loop 0 Arbint.zero handle Div => () | ProgTimeout => ();
    val v = Vector.fromList (rev (!l))
  in
    ccache := dadd p v (!ccache)
  end

fun create_ccache p =
  let 
    val ccache = ref (dempty prog_compare)
    val comprl = dict_sort prog_compare_size (all_subcompr p)
  in
    app (add_ccache ccache) comprl;
    !ccache
  end

fun mk_exec p = let val ccache = create_ccache p in mk_exec_aux ccache p end
fun coverp_oeis p = cover_oeis (mk_exec p) 
fun coverp_target p target = cover_target (mk_exec p) target

(* -------------------------------------------------------------------------
   Sequences generated by a program up to a number n.
   Time limit of 1.0 seconds with no increment.
   ------------------------------------------------------------------------- *)

fun penum p n = 
  let 
    val _ = timeincr := long_timeincr
    val f = mk_exec p
    val _ = init_timer ()
    val _ = timelimit := 1.0
    val l = ref []
    fun loop i x = if i >= n then () else
      (
      l := f (x, Arbint.zero) :: !l; incr_timer ();
      loop (i+1) (Arbint.+ (x,Arbint.one))
      )
    val _ = loop 0 Arbint.zero handle Div => () | ProgTimeout => ();  
  in  
    timeincr := short_timeincr;
    rev (!l)
  end
  
(* -------------------------------------------------------------------------
   Caching OEIS sequences
   -------------------------------------------------------------------------
*)  

fun penumt p n = 
  let 
    val f = mk_exec p 
    val _ = init_timer ()
    val l = ref []
    fun loop i x = 
      if i >= n then () else
      (
      l := f (x, Arbint.zero) :: !l; 
      incr_timer ();
      loop (i+1) (Arbint.+ (x,Arbint.one))
      )
    val _ = loop 0 Arbint.zero handle Div => () | ProgTimeout => ()  
  in  
    rev (!l)
  end

end (* struct *)

(* 
load "exec"; open exec; 
load "human"; open kernel human aiLib;
val p =  parse_human "(loop ( * 2 x) (+ x 2) 1)";
val p = parse_human "(+ (compr (% (- (loop ( * 2 x) (+ x 1) 1) 1) (+ x 2val (l1,t) = add_time (penum p) 5;)) x) 2"; 
humanf p;
val (l1,t) = add_time (penum p) 30;

*)
