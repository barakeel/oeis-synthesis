structure exec_intl :> exec_intl =
struct

open HolKernel boolLib aiLib kernel bloom
val ERR = mk_HOL_ERR "exec_intl"
type prog = kernel.prog
type exec = IntInf.int list * IntInf.int list * IntInf.int list -> 
  IntInf.int list

(* -------------------------------------------------------------------------
   Time limit
   ------------------------------------------------------------------------- *)

local open IntInf in
  val azero = fromInt 0
  val aone = fromInt 1
  val atwo = fromInt 2
  val athree = fromInt 3
  val afour = fromInt 4
  val afive = fromInt 5
  val asix = fromInt 6
  val aseven = fromInt 7
  val aeight = fromInt 8
  val anine = fromInt 9
  val aten = fromInt 10  
  fun aincr x = x + aone
  fun adecr x = x - aone
  fun arb_pow a b = if b <= azero then aone else a * arb_pow a (b-aone)
  fun pow2 b = arb_pow atwo (fromInt b)
  val maxarb = arb_pow (fromInt 10) (fromInt 285) (* 4.685 * 10 ^ 284 *)
  val minarb = ~maxarb
  val maxint = fromInt (valOf (Int.maxInt))
  val minint = fromInt (valOf (Int.minInt))
  fun large_arb x = x > maxarb orelse x < minarb
  fun large_int x = x > maxint orelse x < minint
end

val verylargeint = int_pow 2 40
val smallcost_flag = ref false

fun cost costn x = 
  if !smallcost_flag then
    if x > aone orelse x < ~aone
    then 
      let val size = IntInf.log2 (IntInf.abs x) in
        if size > 1024 then verylargeint else costn * size
      end
    else costn
  else 
    if large_int x 
    then 
      let val cost1 = IntInf.log2 (IntInf.abs x) in
        if cost1 > 1024 then verylargeint else cost1
      end
    else costn

fun testn costn f x =
  let 
    val y = f x 
    val _ = abstimer := !abstimer + cost costn (hd y)   
  in
    if !abstimer > !timelimit then raise ProgTimeout else y
  end
    
fun test f x = testn 1 f x

fun testcache costn y = 
  let val _ = abstimer := !abstimer + costn in
    if !abstimer > !timelimit then raise ProgTimeout else y
  end

(* -------------------------------------------------------------------------
   Time limit wrappers
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

(* -------------------------------------------------------------------------
   Basic intructions
   ------------------------------------------------------------------------- *)
 
val zero_f = mk_nullf (fn _ => [azero])
val one_f = mk_nullf (fn _ => [aone])
val two_f = mk_nullf (fn _ => [atwo])
val x_f = mk_nullf (fn (x,y,z) => x)
val y_f = mk_nullf (fn (x,y,z) => y)

fun mk_e f (l1,l2) = case (l1,l2) of
    ([],_) => raise Div
  | (_,[]) => raise Div
  | (a1 :: m1, a2 :: m2) => (f (a1,a2) :: m1)
  
val addi_f = mk_binf 1 (mk_e (op +))
val diff_f = mk_binf 1 (mk_e (op -))
val mult_f = mk_binf 1 (mk_e (op *))
val divi_f = mk_binf 5 (mk_e (op div))
val modu_f = mk_binf 5 (mk_e (op mod))

fun cond_f fl = case fl of
   [f1,f2,f3] => 
      (fn x =>
       let 
         val y = if hd (f1 x) <= azero then f2 x else f3 x
         val _ = abstimer := !abstimer + 1  
       in
         if !abstimer > !timelimit then raise ProgTimeout else y
       end)
  | _ => raise ERR "mk_condf" ""


fun cat_f fl = case fl of
   [f1,f2] => 
      (fn x =>
       let 
         val y1 = f1 x 
         val y2 = f2 x
         val y = y1 @ y2
         val yn = length y
         val _ = abstimer := !abstimer + yn  
       in
         if !abstimer > !timelimit 
         then raise ProgTimeout 
         else if yn >= 100 then raise Div else y 
       end)
  | _ => raise ERR "mk_catf" ""

fun pop_f fl = case fl of
   [f] => 
      (fn x =>
       let 
         val y = f x
         val _ = abstimer := !abstimer + 1  
       in
         if !abstimer > !timelimit then raise ProgTimeout else 
           (case y of [] => raise Empty | [a] => [a] | a :: m => m)
       end)
  | _ => raise ERR "mk_popf" ""


(* -------------------------------------------------------------------------
   Loops
   ------------------------------------------------------------------------- *)
   
fun loop3_f_aux f1 f2 f3 n x1 x2 x3 = 
  if n <= azero then x1 else loop3_f_aux f1 f2 f3 (adecr n) 
  (f1 (x1,x2,x3)) (f2 (x1,x2,x3)) (f3 (x1,x2,x3))
fun loop3_f_aux2 (f1,f2,f3,n,x1,x2,x3) = loop3_f_aux f1 f2 f3 (hd n) x1 x2 x3
val loop3_f = mk_septf3 loop3_f_aux2

fun loop2_f_aux (f1,f2,n,x1,x2) = 
  loop3_f_aux f1 f2 (fn (x1,x2,x3) => [aincr (hd x3)]) (hd n) x1 x2 [aone]
val loop2_f = mk_quintf2 loop2_f_aux

fun loop_f_aux (f1,n,x1) = 
  loop3_f_aux f1 (fn (x1,x2,x3) => [aincr (hd x2)]) (fn (x1,x2,x3) => x3) 
    (hd n) x1 [aone] x1
val loop_f = mk_ternf1 loop_f_aux

fun create_compr f =
  let
    val _ = init_timer ()
    val prevtime = ref (!abstimer)
    val l = ref []
    fun loop i x =
      if i >= !max_compr_number then () else
      if hd (f (x,[azero], [azero])) <= azero
      then (
           l := (x,!abstimer - !prevtime) :: !l; 
           prevtime := !abstimer;
           incr_timer (); 
           loop (i+1) [aincr (hd x)]
           ) 
      else loop i [aincr (hd x)]
    val _ = catch_perror (loop 0) [azero] (fn () => ())
    val v = Vector.fromList (rev (!l))
    (* val _ = print_endline ("len: " ^ its (Vector.length v)) *)
  in
    (fn x => if x < 0 then raise Div 
             else if x >= Vector.length v then raise ProgTimeout
             else Vector.sub (v,x))
  end

fun compr_f fl = case fl of
  [f1,f2] =>
  let 
    val f1' = create_compr f1 in
    (fn x =>
     let 
       val input = IntInf.toInt (hd (f2 x)) handle Overflow => raise Div 
       val (y,cost) = f1' input
     in
       testcache cost y
     end)
  end
  | _ => raise ERR "compr_f" ""


(* -------------------------------------------------------------------------
   Instruction sets
   ------------------------------------------------------------------------- *)

val org_execl = 
  [zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,cond_f,
   loop_f,x_f,y_f, compr_f,loop2_f]

val execv = Vector.fromList (org_execl @ [cat_f, pop_f])

val _ = if Vector.length execv <> Vector.length operv
        then raise ERR "execv" "mismatch with operv"
        else ()

(* -------------------------------------------------------------------------
   Execute a program
   ------------------------------------------------------------------------- *)

fun mk_exec_move id fl = Vector.sub (execv,id) fl
  
fun mk_exec (p as (Ins (id,pl))) = 
  let val fl = map mk_exec pl in mk_exec_move id fl end

fun coverf_oeis exec = 
  let fun g x = hd (exec ([x], [azero], [azero])) in
    cover_oeis g
  end

fun mk_exec_onev p = 
  let val f = mk_exec p in (fn x => hd (f ([x],[azero],[azero]))) end
  
(* -------------------------------------------------------------------------
   Verifiy cover
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
  
fun penum_wtime r p n = (timeincr := r; penum_aux p n) 
  
fun verify_wtime r (anum,p) = 
  let 
    val seq1 = valOf (Array.sub (bloom.oseq, anum)) 
    val seq2 = penum_wtime r p (length seq1)
  in
    (seq1 = seq2, is_prefix seq2 seq1)
  end

end (* struct *)


(* -------------------------------------------------------------------------
   Verifying that new code accept old solutions
   ------------------------------------------------------------------------- *)

(*
load "exec_intl";  open kernel aiLib exec_intl;

val itsol = read_itprogl "model/itsol209"; 
val isol = random_subset 2000 (map (fn (x,(_,y)) => (x,y)) (distrib itsol)); 
length isol;

init_slow_test ();
val bbl = map_assoc (verify_wtime 1000000) isol;
val lbad1 = filter (not o fst o snd) bbl; length lbad1;
val lbad2 = filter (not o snd o snd) bbl; length lbad2;
val lbad = map fst lbad1;
length lbad;

fun f (i,p) = its i ^ ": " ^ humanf p;
map f lbad;
write_iprogl "lbad" lbad;
val lbad = read_iprogl "lbad";
*)

(* -------------------------------------------------------------------------
   Testing
   ------------------------------------------------------------------------- *) 
    
(* 
load "exec"; open exec; 
load "human"; open kernel human aiLib;
val p =  parse_human "(loop ( * 2 x) (+ x 1)";
val p = parse_human "(loop ( * x x) x  2)";
val p = parse_human "(% x 2)";
val p = parse_human "(% (- (loop ( * 2 x) x 1) 2) x) "; 
humanf p;
val f = mk_exec_prime p;
List.tabulate (10, fn x => f (x + 3));
val f = mk_exec_onev p;
List.tabulate (10, fn x => f (IntInf.fromInt (x + 3)));

val (l1,t) = add_time (penum p) 7;
!abstimer;
val l = penum_prime p;
!abstimer;
*)

(* -------------------------------------------------------------------------
   Find stat
   ------------------------------------------------------------------------- *) 

(* 
load "kernel"; open kernel aiLib;
load "exec"; open exec;
load "human";  open human;
load "bloom"; open bloom;

val itsol20 = read_itprogl "itsol20";
length itsol20;

val progl = map (snd o singleton_of_list o snd) itsol20;
val l = 
  first_n 4 (
  dict_sort compare_imax (dlist (count_dict (dempty prog_compare)  progl)));

val prog = fst (List.nth (l,1));

val f = create_fsf (mk_exec prog);
List.tabulate (33, fn x =>  IntInf.toInt (f (IntInf.fromInt x)));
*)


     
