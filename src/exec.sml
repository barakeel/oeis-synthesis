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
val smallcost_flag = ref true

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
    val _ = abstimer := !abstimer + cost costn y   
  in
    if !abstimer > !timelimit then raise ProgTimeout else y
  end
    
fun test f x = testn 1 f x

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

(* only caching ones that do not depend on y or z *)
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
  
fun verify_eq (r,n) (p1,p2) =
  let 
    val seq1 = penum_wtime r p1 n
    val seq2 = penum_wtime r p2 n
  in
    is_prefix seq2 seq1 orelse is_prefix seq1 seq2
  end

(* -------------------------------------------------------------------------
   Prime approximations enumerations
   ------------------------------------------------------------------------- *)

fun is_prime x = not
  (exists (fn i => x mod i = 0) (List.tabulate (x-2, (fn x => x + 2))));
val primel = map_assoc is_prime (List.tabulate (1000 - 3, fn x => x + 3));
val primev = Vector.fromList ([false,false,true] @ map snd primel);

val offset_prime = 3 
val offset_list = List.tabulate (offset_prime, fn _ => (azero,0))  
  
fun cache_exec_prime exec bonus l = 
  let val v = Vector.fromList (offset_list @ l) in
    fn x =>
    let val no = SOME (IntInf.toInt (#1 x)) handle Overflow => NONE in
      case no of NONE => exec x | SOME n => 
      if n = Vector.length v andalso !abstimer + bonus > !timelimit
        then raise ProgTimeout 
      else
      if n >= offset_prime andalso n < Vector.length v then 
        let val (r,tim) = Vector.sub (v,n) in
          testcache tim r
        end
      else exec x    
    end
  end

val prime_found = ref false

fun penum_prime_exec exec = 
  let 
    val _ = prime_found := false
    val _ = timeincr := 20000
    val _ = init_timer ()
    val starttim = ref 0
    fun f x = 
      let 
        val _ = starttim := !abstimer 
        val r = exec (IntInf.fromInt x, azero, azero)
      in
        (r, !abstimer - !starttim)
      end 
    fun mk_b i (r,_) = (r <= azero) = Vector.sub (primev,i)
    val (ngood,nbad,ntot) = (ref 0, ref 0, ref 0)
    val l = ref []
    val bgood = ref false
    fun loop i = 
      if i >= 64 then (bgood := true; starttim := !abstimer) else
      if (!ngood) < (!ntot) - 1 then starttim := !abstimer else
      let
        val x = f i 
        val b = mk_b i x  
      in
        l := x :: !l;
        if b then incr ngood else incr nbad;
        incr ntot;
        incr_timer ();
        loop (i+1)
      end
    val _ = catch_perror loop offset_prime (fn () => ())
  in  
    (if !bgood then (prime_found := true; map fst (rev (!l))) else [],
     cache_exec_prime exec (!abstimer - !starttim) (rev (!l)))
  end

(* -------------------------------------------------------------------------
   Hadamard (maybe use hash function)
   ------------------------------------------------------------------------- *)

fun scalar_product l1 l2 =
  sum_int (map (fn (x,y) => x * y) (combine (l1,l2)))

fun orthogonal l1 l2 = scalar_product l1 l2 = 0
val hash_modulo = 79260655 * 10000000 + 5396977

fun hash acc l = case l of
    [] => acc
  | 1 :: m => hash ((2 * acc + 1) mod hash_modulo) m
  | ~1 :: m => hash ((2 * acc) mod hash_modulo) m
  | _ :: m => raise ERR "hash_hdmseq" ""

fun score_table table = 
  let 
    val l1 = map (uncurry scalar_product) (all_pairs table)
    val l2 = map (fn x => if x = 0 then 1 else 0) l1
  in
    sum_int l2
  end

fun penum_hadamard exec ztop = 
  let
    (* timers *)
    val _ = timeincr := 20000
    val _ = init_timer ()
    val starttim = ref 0
    (* results *)
    val result = ref []
    val cresult = ref []
    val table = ref []
    val b = ref false
    fun f (x,y,z) =
      let 
        val _ = starttim := !abstimer 
        val r = exec (IntInf.fromInt x, IntInf.fromInt y, IntInf.fromInt z)
      in
        if r <= 0 then 1 else ~1
      end
    val table = List.tabulate (ztop, 
      fn y => (List.tabulate (ztop, fn x => 
        let val r = f(x,y,ztop) in incr_timer (); r end)))
    val sc = score_table table
    val h = hash 1 (List.concat table)
  in   
    map IntInf.fromInt [h,ztop,sc]
  end
  handle Div => [] 
       | ProgTimeout => [] 
       | Overflow => []



end (* struct *)

(* -------------------------------------------------------------------------
   Verifying that new code accept old solutions
   ------------------------------------------------------------------------- *)

(*
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
