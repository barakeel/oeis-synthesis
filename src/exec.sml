structure exec :> exec =
struct

open HolKernel boolLib aiLib kernel bloom
val ERR = mk_HOL_ERR "exec"
type prog = kernel.prog
type exec = IntInf.int * IntInf.int * IntInf.int -> IntInf.int

(* -------------------------------------------------------------------------
   Time limit
   ------------------------------------------------------------------------- *)

val maxint1 = valOf (Int.maxInt)

local open IntInf in
  val azero = fromInt 0
  val aone = fromInt 1
  val atwo = fromInt 2
  fun aincr x = x + aone
  fun adecr x = x - aone
  fun aleq a b = a <= b
  fun arb_pow a b = if b <= azero then aone else a * arb_pow a (b-aone)
  fun pow2 b = arb_pow atwo (fromInt b)
  val maxarb = arb_pow (fromInt 10) (fromInt 285) (* 4.685 * 10 ^ 284 *)
  val minarb = ~maxarb
  val maxint = fromInt maxint1
  val minint = ~maxint
  fun large_arb x = x > maxarb orelse x < minarb
  fun large_int x = x > maxint orelse x < minint
end 

val verylargeint = int_pow 2 40

fun cost costn x = 
  if large_int x 
  then 
    let val cost1 = IntInf.log2 (IntInf.abs x) in
      if cost1 > 1024 then verylargeint else cost1
    end
  else costn

fun testn costn f x =
  let 
    val y = f x 
    val _ = abstimer := !abstimer + cost costn y   
  in
    if !abstimer > !timelimit then raise ProgTimeout else y
  end
  
fun test f x =
  let 
    val y = f x 
    val _ = abstimer := !abstimer + cost 1 y   
  in
    if !abstimer > !timelimit then raise ProgTimeout else y
  end

fun testcache costn y = 
  let val _ = abstimer := !abstimer + costn in
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

fun mk_binf costn opf fl = 
  case fl of
   [f1,f2] => (fn x => (testn costn opf (f1 x, f2 x)))
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

(* functions *)
local open IntInf in
  val zero_f = mk_nullf (fn _ => azero)
  val one_f = mk_nullf (fn _ => aone)
  val two_f = mk_nullf (fn _ => atwo)
  val x_f = mk_nullf (fn (x,y,z) => x)
  val y_f = mk_nullf (fn (x,y,z) => y)
  val z_f = mk_nullf (fn (x,y,z) => z)
  val addi_f = mk_binf 1 (op +)
  val diff_f = mk_binf 1 (op -)
  val mult_f = mk_binf 1 (op *)
  val divi_f = mk_binf 5 (op div)
  val modu_f = mk_binf 5 (op mod)
  fun cond_f_aux (a,b,c) = if a <= azero then b else c
  val cond_f = mk_ternf cond_f_aux
end (* local *)


(* loops *)
fun loop3_f_aux f1 f2 f3 n x1 x2 x3 = 
  if aleq n azero then x1 else 
  loop3_f_aux f1 f2 f3 (adecr n) 
  (f1 (x1,x2,x3)) (f2 (x1,x2,x3)) (f3 (x1,x2,x3))
fun loop3_f_aux2 (f1,f2,f3,n,x1,x2,x3) = loop3_f_aux f1 f2 f3 n x1 x2 x3
val loop3_f = mk_septf3 loop3_f_aux2

fun loop2_f_aux (f1,f2,n,x1,x2) = 
  loop3_f_aux f1 f2 (fn (x1,x2,x3) => aincr x3) n x1 x2 aone
val loop2_f = mk_quintf2 loop2_f_aux

fun loop_f_aux (f1,n,x1) = 
  loop3_f_aux f1 (fn (x1,x2,x3) => aincr x2) (fn (x1,x2,x3) => x3) n x1 aone x1
val loop_f = mk_ternf1 loop_f_aux

(* comprehension *)
fun create_compr f =
  let
    val _ = init_timer ()
    val prevtime = ref (!abstimer)
    val l = ref []
    fun loop i x =
      if i >= !max_compr_number then () else
      if aleq (f (x, azero, azero)) azero
      then (
           l := (x,!abstimer - !prevtime) :: !l; 
           prevtime := !abstimer;
           incr_timer (); 
           loop (i+1) (aincr x)
           ) 
      else loop i (aincr x)
    val _ = catch_perror (loop 0) azero (fn () => ())
    val v = Vector.fromList (rev (!l))
    (* val _ = print_endline ("len: " ^ its (Vector.length v)) *)
  in
    (fn x => if x < 0 orelse x >= Vector.length v 
             then raise Div 
             else Vector.sub (v,x))
  end

fun compr_f fl = case fl of
  [f1,f2] =>
  let 
    val f1' = create_compr f1 in
    (fn x =>
     let 
       val input = IntInf.toInt (f2 x) handle Overflow => raise Div 
       val (y,cost) = f1' input
     in
       testcache cost y
     end)
  end
  | _ => raise ERR "compr_f" ""

val execv = Vector.fromList 
  [
  zero_f,one_f,two_f,
  addi_f,diff_f,mult_f,divi_f,modu_f,
  cond_f,loop_f,
  x_f,y_f,
  compr_f, loop2_f,
  z_f, loop3_f
  ]

(* -------------------------------------------------------------------------
   Execute a program
   ------------------------------------------------------------------------- *)

fun mk_exec_move id fl = Vector.sub (execv,id) fl
  
fun mk_exec (p as (Ins (id,pl))) = 
  let val fl = map mk_exec pl in mk_exec_move id fl end

fun cache_exec exec = 
  let 
    val v = Vector.fromList (rev (!graph))
    val b = !graphb
  in
    fn x =>
    let val no = SOME (IntInf.toInt (#1 x)) handle Overflow => NONE in
      case no of NONE => exec x | SOME n => 
      if n = Vector.length v andalso !abstimer + b > !timelimit
        then raise ProgTimeout 
      else 
      if n >= 0 andalso n < Vector.length v 
        then 
          let val (r,tim) = Vector.sub (v,n) in
            testcache tim r
          end
      else exec x    
    end
  end

fun coverf_oeis exec = 
  let
    val _ = graph := []
    val _ = graphb := 0
    val i = ref 0
    fun g x = 
      let
        val r = exec (x, azero, azero)
        val loctime = !abstimer - !i
      in
        i := !abstimer;
        graph := (r,loctime) :: !graph; 
        r
      end
    val r1 = cover_oeis g
    val _ = graphb := !abstimer - !i;
  in
    r1
  end

fun mk_exec_onev p = 
  let val f = mk_exec p in (fn x => f (x, azero, azero)) end
  
fun coverp_target p target = cover_target (mk_exec_onev p) target

(* -------------------------------------------------------------------------
   Sequences generated by a program up to a number n.
   ------------------------------------------------------------------------- *)

fun penum_aux p n = 
  let 
    val f = mk_exec_onev p
    val _ = init_timer ()
    val l = ref []
    fun loop i x = if i >= n then () else
      (
      l := f x :: !l; 
      incr_timer ();
      loop (i+1) (aincr x)
      )
    val _ = catch_perror (loop 0) azero (fn () => ())
  in  
    rev (!l)
  end
  
fun penum p n = (init_slow_test (); penum_aux p n)

fun penum_limit_aux m p n = 
  let 
    val f = mk_exec_onev p
    val _ = init_timer ()
    val l = ref []
    fun loop i x = if aleq m x orelse i >= n then () else
      (
      l := f x :: !l; 
      incr_timer ();
      loop (i+1) (aincr x)
      )
    val _ = catch_perror (loop 0) azero (fn () => ())
  in  
    rev (!l)
  end
 
fun penum_limit m p n = (init_slow_test (); penum_limit_aux m p n)

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
val p =  parse_human "(loop ( * 2 x) (+ x 1)";
val p = parse_human "(+ (compr (% (- (loop ( * 2 x) (+ x 1) 1) 1) (+ x 2)) x) 2)"; 

val p = parse_human "(loop ( * x x) x  2)";
humanf p;
val (l1,t) = add_time (penum p) 7;
!abstimer;

val isol = read_iprogl "model-old/isol100"; length isol;
init_slow_test ();
val bbl = map_assoc (verify_wtime 1000000) isol;

val lbad1 = filter (not o fst o snd) bbl; length lbad1;
val lbad2 = filter (not o snd o snd) bbl; length lbad2;
val lbad = map fst lbad1;
fun f (i,p) = its i ^ ": " ^ humanf p;
map f lbad;

write_iprogl "lbad" lbad;
val lbad = read_iprogl "lbad";

*)
