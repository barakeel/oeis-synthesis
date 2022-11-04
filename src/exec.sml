structure exec :> exec =
struct

open HolKernel boolLib aiLib kernel bloom hadamard
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
 
(* global data *)
val x_current = ref azero
val y_current = ref azero
val z_current = ref azero
val ainit = Vector.tabulate (10000,fn _ => azero)
val array_glob = ref ainit
fun init_array () = array_glob := ainit
fun arinit dim = 
  Vector.tabulate (dim, fn x => Vector.tabulate (dim, fn y => 
    if x = 0 andalso y = 0 then aone else azero))
val xar_glob = ref (arinit 28)
val yar_glob = ref (arinit 28)
(* end global data *)

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

(* hadamard functions *)
val compute_flag = ref false (* dangerous only turn on for verification *)

(* functions *)
fun xarf offx offy = mk_nullf (fn (x,y,z) => 
  Vector.sub (Vector.sub (!xar_glob, IntInf.toInt ((x+offx) mod z)),
    IntInf.toInt ((y+offy) mod z))) 
fun yarf offx offy = mk_nullf (fn (x,y,z) => 
  Vector.sub (Vector.sub (!yar_glob, IntInf.toInt ((x+offx) mod z)),
    IntInf.toInt ((y+offy) mod z))) 

local open IntInf in
  val x11_f = xarf (~1) (~1)
  val x12_f = xarf (~1) 0
  val x13_f = xarf (~1) 1
  val x21_f = xarf 0 (~1)
  val x22_f = xarf 0 0
  val x23_f = xarf 0 1
  val x31_f = xarf 1 (~1)
  val x32_f = xarf 1 0
  val x33_f = xarf 1 1
  val y11_f = yarf (~1) (~1)
  val y12_f = yarf (~1) 0
  val y13_f = yarf (~1) 1
  val y21_f = yarf 0 (~1)
  val y22_f = yarf 0 0
  val y23_f = yarf 0 1
  val y31_f = yarf 1 (~1)
  val y32_f = yarf 1 0
  val y33_f = yarf 1 1
  val not_f = mk_unf (fn a => 1 - a)
  val and_f = mk_binf 1 (fn (a,b) => a * b) 
  val or_f = mk_binf 1 (fn (a,b) => (a + b) - a * b)
  val xor_f = mk_binf 1 (fn (a,b) => (a + b) - 2 * a * b)  
  val zero_f = mk_nullf (fn _ => azero)
  val one_f = mk_nullf (fn _ => aone)
  val two_f = mk_nullf (fn _ => atwo)
  val x_f = mk_nullf (fn (x,y,z) => x)
  val y_f = mk_nullf (fn (x,y,z) => y)
  val z_f = mk_nullf (fn (x,y,z) => z)
  val X_f = mk_nullf (fn (x,y,z) => !x_current)
  val Y_f = mk_nullf (fn (x,y,z) => !y_current)
  val Z_f = mk_nullf (fn (x,y,z) => !z_current) 
  val addi_f = mk_binf 1 (op +)
  val diff_f = mk_binf 1 (op -)
  val mult_f = mk_binf 1 (op *)
  val divi_f = mk_binf 5 (op div)
  val modu_f = mk_binf 5 (op mod)
  fun cond_f_aux (a,b,c) = if a <= azero then b else c
  val cond_f = mk_ternf cond_f_aux
  fun cases_f_aux (a,b,c) = 
    if !y_current = azero then a 
    else if !y_current = aone then b 
    else c
  val cases_f = mk_ternf cases_f_aux
  fun wrapfv2 v (c,a) = 
    if c <= azero orelse c >= fromInt (Vector.length v) then azero else
      IntInf.fromInt (Vector.sub (Vector.sub (v, toInt c), toInt (a mod c)))
  fun wrapfv1 v c = 
    if c < azero orelse c >= fromInt (Vector.length v) then azero else
      IntInf.fromInt (Vector.sub (v,toInt c))
  val sqrt_f = mk_binf 1 (wrapfv2 sqrtv)
  val inv_f = mk_binf 1 (wrapfv2 invv)
  val leastdiv_f = mk_unf (wrapfv1 leastdivv)
  fun array_f_aux a = 
    if a < azero orelse a >= fromInt (Vector.length (!array_glob)) 
    then azero
    else Vector.sub (!array_glob, toInt a)
  val array_f = mk_unf array_f_aux
  fun assign_f_aux (a,b) =
    (
    if a < azero orelse a >= fromInt (Vector.length (!array_glob)) 
      then ()
      else array_glob := Vector.update (!array_glob, toInt a, b);
    azero
    )
  val assign_f = mk_binf 1 assign_f_aux
    
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
             then (if !hadamard_flag then (azero,1) else raise Div) 
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

val execv = 
  if !hadamard_flag then 
    if !convolution_flag then
      Vector.fromList [x11_f (* dummy function *) ,
       x11_f,x12_f,x13_f,x21_f,x22_f,x23_f,x31_f,x32_f,x33_f,
       y11_f,y12_f,y13_f,y21_f,y22_f,y23_f,y31_f,y32_f,y33_f,
       not_f,and_f,or_f,xor_f]  
    else
    Vector.fromList 
    ([zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,
      cond_f,x_f,y_f,z_f] @
    (if !bigvar_flag then [X_f,Y_f,Z_f] else []) @   
    (if !sqrt_flag then [sqrt_f,inv_f,leastdiv_f] else []) @
    (if !loop_flag then [compr_f, loop_f, loop2_f, loop3_f] else [])
    )
  else if !array_flag then Vector.fromList
    [zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,
     cond_f,x_f,y_f,array_f,assign_f,loop_f]
  else 
    Vector.fromList 
    ([zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,
     cond_f,loop_f,x_f,y_f,
     compr_f, loop2_f] @
     (if !z_flag then [z_f, loop3_f] else []))
  
val _ = if Vector.length execv <> Vector.length operv
        then raise ERR "execv" "mismatch with operv"
        else ()

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
   Williamson type hadamard matrices
   ------------------------------------------------------------------------- *)

fun scalar_product l1 l2 =
  sum_int (map (fn (x,y) => x * y) (combine (l1,l2)))

fun orthogonal l1 l2 = scalar_product l1 l2 = 0
val hash_modulo = 486632209873
val hash_moduloi = IntInf.fromInt 486632209873

fun hash_zero h i = (88591 * h + 512872 + i) mod hash_modulo

fun hash_one h i = 
  let val i' = IntInf.toInt (i mod hash_moduloi) in
    (88591 * h + 512871 + i') mod hash_modulo
  end
  
fun hash acc l = case l of
    [] => acc
  | 1 :: m => hash ((88591 * acc + 512871) mod hash_modulo) m
  | ~1 :: m => hash ((69833 * acc + 47303) mod hash_modulo) m
  | _ :: m => raise ERR "hash_hdmseq" ""

fun norm_table table =
  let fun norm_vect l = if hd l = ~1 then map (fn x => ~1 * x) l else l in
    dict_sort (list_compare Int.compare) (map norm_vect table) 
  end

fun hash_table table = hash 1 (List.concat (norm_table table))

fun norm_line l = if hd l = 1 then l else map (fn x => ~1 * x) l

fun penum_hadamard_once h exec ztop = 
  let
    val fi = IntInf.fromInt
    (* results *)
    fun f (x,y,z) =
      let
        val _ = init_timer ()
        val _ = (x_current := fi x; y_current := fi y; z_current := fi z)
        val r = exec (fi x, fi y, fi z)
      in
        if r <= 0 then 1 else ~1
      end
    fun genline y = List.tabulate (ztop, fn x => f(x,y,ztop))
    val v0 = Vector.fromList (norm_line (genline 0))
    val v1 = Vector.fromList (norm_line (genline 1))
    val v2 = Vector.fromList (norm_line (genline 2))
    val v3 = Vector.tabulate (ztop, fn i => 
      if i = 0 then 1 else 
      let val sum = 
        Vector.sub (v0,i) + Vector.sub (v1,i) + Vector.sub (v2,i)
      in
        if sum = 3 then ~1 else 
        if sum = ~3 then 1
        else if sum > 0 then 1 else ~1
      end)
    val sc = wilson_score3 (v0,v1,v2,v3)
    val _ = h := hash (!h) (vector_to_list (Vector.concat [v0,v1,v2,v3]))
  in   
    (sc,(v0,v1,v2,v3))
  end

fun value acc l = case l of
    [] => acc 
  | ~1 :: m => value (2*acc) m
  | 1 :: m => value (2*acc+1) m
  | _ :: m => raise ERR "value" ""
  
fun rotate_back l = tl l @ [hd l]  

fun value_vl (l0,l1,l2,l3) = 
  value 0 l0 + value 0 l1 + value 0 l2 + value 0 l3

fun norm_vl n (bestvl,bestsc) (l0,l1,l2,l3) =
  if n <= 0 then bestvl else
  let 
    val newvl = 
      (rotate_back l0, rotate_back l1, rotate_back l2, rotate_back l3) 
    val newsc = value_vl newvl  
  in
    norm_vl (n-1) (if newsc > bestsc then (newvl,newsc) else (bestvl,bestsc))
      newvl
  end  
  
fun norm_vl_full (v0,v1,v2,v3) =
  let 
    val n = Vector.length v0 
    val bestvl = 
      (vector_to_list v0, vector_to_list v1, 
       vector_to_list v2, vector_to_list v3)
    val bestsc = value_vl bestvl
    val (l1,l2,l3,l4) = norm_vl (n-1) (bestvl,bestsc) bestvl  
  in
    List.concat (dict_sort (list_compare Int.compare) [l1,l2,l3,l4])
  end 
  
fun penum_hadamard exec =
  let
    val h = ref 1
    val scl = List.tabulate (10, fn x => penum_hadamard_once h exec (2*x + 7))
    val sortedscl = dict_sort (fst_compare Int.compare) scl
    val ((a,vla),(b,vlb)) = pair_of_list (first_n 2 sortedscl)
    val h = hash 1 (norm_vl_full vla @ norm_vl_full vlb)
  in
    map IntInf.fromInt ([a + b, h] @ map fst scl)
  end
  handle Div => [] | ProgTimeout => [] | Overflow => []

(* -------------------------------------------------------------------------
   Hadamard matrices
   ------------------------------------------------------------------------- *)

fun scalv l1 l2 = sum_int (map (fn (x,y) => x * y) (combine (l1,l2)))
fun perp l1 l2 = (scalv l1 l2 = 0)

fun penum_real_hadamard_once exec ztop = 
  let
    val fi = IntInf.fromInt
    (* results *)
    fun f (x,y,z) =
      let
        val _ = init_timer ()
        val _ = (x_current := fi x; y_current := fi y; z_current := fi z)
        val r = exec (fi x, fi y, fi z)
      in
        if r <= 0 then 1 else ~1
      end
    fun genline y = List.tabulate (ztop, fn x => f(x,y,ztop))
    fun loop set ytop =
      if ytop = ztop then ytop else
      let val line = genline ytop in
        if not (all (perp line) set) then ytop 
        else loop (line :: set) (ytop + 1)
      end
    val sc' = loop [] 0
    val sc = if sc' <= 1 then 0 else sc'
  in   
    (sc * 10000) div ztop
  end
  handle Div => ~1 | ProgTimeout => ~2 | Overflow => ~3
  
fun penum_real_hadamard exec =
  let 
    val scl = map (penum_real_hadamard_once exec)
      (List.tabulate (10, fn x => 4*(2*x+7)))
    val sortedscl = rev (dict_sort Int.compare scl)
    val bestsc = hd sortedscl
  in
    if bestsc <= 0 then [] else map IntInf.fromInt (sortedscl @ scl)
  end

(* -------------------------------------------------------------------------
   Hadamard matrices generated via convolution
   ------------------------------------------------------------------------- *)

fun score_aux table count set xtop =
  if xtop = Vector.length table then count else
  let 
    val line = Vector.sub (table,xtop) 
    val newcount = length (filter (perp line) set)  
  in
    score_aux table newcount (line :: set) (xtop + 1)
  end

fun hash acc l = case l of
    [] => acc
  | 1 :: m => hash ((591 * acc + 871) mod 1000) m
  | ~1 :: m => hash ((833 * acc + 303) mod 1000) m
  | _ :: m => raise ERR "hash_hdmseq" ""

fun hash_table table = hash 1 (List.concat (vector_to_list table))

fun score_table table = 
  let 
    val dim = Vector.length table
    val sc = score_aux table 0 [] 0 
  in
    if sc <= 0 
    then hash_table table
    else (sc * 10000 * 10000) div ((dim * (dim - 1)) div 2)
  end
 
fun penum_conv_hadamard_once (exec1,exec2,exec3) ztop = 
  let
    val arinitz = arinit ztop 
    val _ = (xar_glob := arinitz; yar_glob := arinitz)
    val fi = IntInf.fromInt
    (* results *)
    fun f1 (x,y) = (init_timer (); exec1 (fi x, fi y, fi ztop))
    fun f2 (x,y) = (init_timer (); exec2 (fi x, fi y, fi ztop))
    fun f3 (x,y) = (init_timer (); 
      let val r = exec3 (fi x, fi y, fi ztop) in 
        if r <= azero then 1 else ~1
      end)
    fun update () = 
      let
        val new_xar = 
          Vector.tabulate (ztop, 
            fn x => Vector.tabulate (ztop, fn y => f1 (x,y)))
        val _ = xar_glob := new_xar
        val new_yar = 
          Vector.tabulate (ztop, 
            fn x => Vector.tabulate (ztop, fn y => f2 (x,y)))
        val _ = yar_glob := new_yar
      in
        ()
      end
    fun get_table () =
      Vector.tabulate (ztop, fn x => List.tabulate (ztop, fn y => f3 (x,y))) 
    val _ = funpow ztop update ()
    val table1 = get_table () 
    val _ = funpow ztop update ()
    val table2 = get_table ()
    val _ = funpow ztop update ()
    val table3 = get_table ()
    val _ = funpow ztop update ()
    val table4 = get_table ()  
    val tablescl = map_assoc score_table [table1,table2,table3,table4]
  in   
    snd (hd (dict_sort compare_imax tablescl))
  end
  handle Div => ~1 | ProgTimeout => ~2 | Overflow => ~3
  
fun penum_conv_hadamard (exec1,exec2,exec3) =
  let 
    val scl = map (penum_conv_hadamard_once (exec1,exec2,exec3))
      (List.tabulate (5, fn x => 4*(2*x+7)))
    val sortedscl = rev (dict_sort Int.compare scl)
    val bestsc = hd sortedscl
  in
    if bestsc <= 0 then [] else map IntInf.fromInt (sortedscl @ scl)
  end



end (* struct *)

(* -------------------------------------------------------------------------
   Verifying hadamard function
   ------------------------------------------------------------------------- *)

(*
load "exec"; open exec; 
load "human"; open human aiLib;
val itsol = kernel.read_primel "model/itsol20"; 
fun test x ([a,b,c],d) = (b = IntInf.fromInt x) andalso c = b;
val (a,(b,sol)) = hd (filter (test 28) itsol);
humanf sol;

fun ishdm (_,l) = case l of [a,b,c] => b=c | _ => false;

val r = time (penum_hadamard_online 10000 (mk_exec sol)) 636;

val il = filter ishdm (map (penum_hadamard_online 10000 (mk_exec sol)) 
  (List.tabulate (50,fn x => 4* (x+1))));

val il2 = map snd il;
*)


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
