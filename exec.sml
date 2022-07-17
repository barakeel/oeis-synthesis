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
  fun pow2 b = arb_pow two (fromInt b)
  val maxarb = arb_pow (fromInt 10) (fromInt 285) (* 4.685 * 10 ^ 284 *)
  val minarb = ~maxarb
  val maxint = arb_pow (fromInt 2) (fromInt 64)
  val minint = ~maxint
  fun large_arb x = x > maxarb orelse x < minarb
  fun large_int x = x > maxint orelse x < minint
end 

val costl = map_fst pow2 [(62,50),(128,100),(256,200),(512,400),
  (1024,int_pow 2 40)]

local open Arbint in
  fun cost x = 
    let fun loop cost l = case l of 
        [] => cost
      | (a,b) :: m => if x < a andalso x > ~a then cost else loop b m
    in
      loop 1 costl 
    end
end

fun test f x =
  let 
    val y = f x 
    val _ = abstimer := !abstimer + cost y   
  in
    if !abstimer > !timelimit then raise ProgTimeout else y
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

fun mk_septf3 opf fl = case fl of
   [f1,f2,f3,f4,f5,f6,f7] => 
   (fn x => (test opf (f1, f2, f3, f4 x, f5 x, f6 x, f7 x)))
  | _ => raise ERR "mk_septf3" ""

local open Arbint in

(* first-order *)
val zero_f = mk_nullf (fn _ => zero)
val one_f = mk_nullf (fn _ => one)
val two_f = mk_nullf (fn _ => two)
val x_f = mk_nullf (fn (x,y,z) => x)
val y_f = mk_nullf (fn (x,y,z) => y)
val z_f = mk_nullf (fn (x,y,z) => z)
val addi_f = mk_binf (op +)
val diff_f = mk_binf (op -)
val mult_f = mk_binf (op *)
val divi_f = mk_binf (op div)
val modu_f = mk_binf (op mod)
fun cond_f_aux (a,b,c) = if a <= zero then b else c
val cond_f = mk_ternf cond_f_aux

(* higher-order *)
fun loop3_f_aux f1 f2 f3 n x1 x2 x3 = 
  if n <= zero then x1 else 
  loop3_f_aux f1 f2 f3 (n-one) (f1 (x1,x2,x3)) (f2 (x1,x2,x3)) (f3 (x1,x2,x3))
fun loop3_f_aux2 (f1,f2,f3,n,x1,x2,x3) = loop3_f_aux f1 f2 f3 n x1 x2 x3
val loop3_f = mk_septf3 loop3_f_aux2

fun loop2_f_aux (f1,f2,n,x1,x2) = 
  loop3_f_aux f1 f2 (fn (x1,x2,x3) => x3 + one) n x1 x2 one
val loop2_f = mk_quintf2 loop2_f_aux

fun loop_f_aux (f1,n,x1) = 
  loop3_f_aux f1 (fn (x1,x2,x3) => x2 + one) (fn (x1,x2,x3) => x3) n x1 one x1
val loop_f = mk_ternf1 loop_f_aux

(* compr *)
fun compr_f_cache v f2 x = 
  let val input = Arbint.toInt (f2 x) handle Overflow => raise Div in
    if Int.< (input,0) orelse Int.>= (input, Vector.length v) 
    then raise Div 
    else test Vector.sub (v,input)
  end


end (* local *)

val base_execl =
  [
  zero_f,one_f,two_f,
  addi_f,diff_f,mult_f,divi_f,modu_f,
  cond_f,loop_f,
  x_f,y_f,
  x_f (* placeholder *), loop2_f,
  z_f, loop3_f
  ]
   
val execv = Vector.fromList base_execl

(* -------------------------------------------------------------------------
   Execute a program on some inputs with auto-initialization of compr
   ------------------------------------------------------------------------- *)

fun mk_exec_aux ccache (p as (Ins (id,pl))) = 
  let val fl = map (mk_exec_aux ccache) pl in
    if id = 12 then
      let val v = dfind (hd pl) ccache handle NotFound =>
        raise ERR "mk_exec_aux" (raw_prog p)
      in compr_f_cache v (hd (tl fl)) end 
    else (Vector.sub (execv,id) fl
          handle Subscript => raise ERR "mk_exec_aux" (its id))
  end

val azero = Arbint.zero
val aone = Arbint.one

fun add_ccache ccache p =
  if dmem p (!ccache) then () else
  let
    val _ = init_timer ()
    val f = mk_exec_aux (!ccache) p
    val l = ref []
    fun loop i x =
      if i >= (!max_compr_number) then () else
      if Arbint.<= (f (x, azero, azero), azero)
      then (l := x :: !l; incr_timer (); loop (i+1) (Arbint.+ (x,aone))) 
      else  loop i (Arbint.+ (x,aone))
    val _ = catch_perror (loop 0) azero (fn () => ())
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

fun mk_exec p = 
  let
    val ccache = create_ccache p
    val f = mk_exec_aux ccache p
    fun g x = f (x, azero, azero)
  in 
    g
  end

fun coverp_oeis p = cover_oeis (mk_exec p) 
fun coverp_target p target = cover_target (mk_exec p) target

(* -------------------------------------------------------------------------
   Sequences generated by a program up to a number n.
   ------------------------------------------------------------------------- *)

fun penum_aux p n = 
  let 
    val f = mk_exec p
    val _ = init_timer ()
    val l = ref []
    fun loop i x = if i >= n then () else
      (
      l := f x :: !l; 
      incr_timer ();
      loop (i+1) (Arbint.+ (x,Arbint.one))
      )
    val _ = catch_perror (loop 0) Arbint.zero (fn () => ())
  in  
    rev (!l)
  end
  
fun penum p n = (init_slow_test (); penum_aux p n)
fun penum_wtime r p n = (timeincr := r; penum_aux p n)

(* -------------------------------------------------------------------------
   Verifiy cover
   ------------------------------------------------------------------------- *)  
  
fun verify_wtime r (anum,p) = 
  let 
    val seq1 = valOf (Array.sub (bloom.oseq, anum)) 
    val seq2 = penum_wtime r p (length seq1)
  in
    (seq1 = seq2, is_prefix seq2 seq1)
  end
  
   

end (* struct *)

(* 
load "exec"; open exec; 
load "human"; open kernel human aiLib;
val p =  parse_human "(loop ( * 2 x) (+ x 2) 1)";
val p = parse_human "(+ (compr (% (- (loop ( * 2 x) (+ x 1) 1) 1) (+ x 2val (l1,t) = add_time (penum p) 5;)) x) 2"; 
humanf p;
val (l1,t) = add_time (penum p) 30;
val isol = read_iprogl "model/isol100"; length isol;
val bbl = map_assoc verify isol;

val lbad1 = filter (not o fst o snd) bbl; length lbad1;
val lbad2 = filter (not o snd o snd) bbl; length lbad2;
val lbad = map fst lbad1;
write_iprogl "lbad" lbad;
val lbad = read_iprogl "lbad";
val lbad3 = map_assoc (verify_wtime 1.0) lbad;

*)
