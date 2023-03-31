structure exec :> exec =
struct

open HolKernel boolLib aiLib kernel bloom
val ERR = mk_HOL_ERR "exec"
type prog = kernel.prog
type exec = IntInf.int * IntInf.int * IntInf.int -> IntInf.int

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
  fun aleq a b = a <= b
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
fun init_arr2 dim = 
  Vector.tabulate (dim, fn x => Vector.tabulate (dim, fn y => azero))
val arr2_glob = ref (init_arr2 41)
fun init_arr1 dim = Vector.tabulate (dim, fn _ => azero)
val arr1_glob = ref (init_arr1 28)

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

local open IntInf in
  val zero_f = mk_nullf (fn _ => azero)
  val one_f = mk_nullf (fn _ => aone)
  val two_f = mk_nullf (fn _ => atwo)
  val three_f = mk_nullf (fn _ => athree)
  val four_f = mk_nullf (fn _ => afour)
  val five_f = mk_nullf (fn _ => afive)
  val six_f = mk_nullf (fn _ => asix)
  val seven_f = mk_nullf (fn _ => aseven)
  val eight_f = mk_nullf (fn _ => aeight)
  val nine_f = mk_nullf (fn _ => anine)
  val ten_f = mk_nullf (fn _ => aten)
  val x_f = mk_nullf (fn (x,y,z) => x)
  val y_f = mk_nullf (fn (x,y,z) => y)
  val z_f = mk_nullf (fn (x,y,z) => z)
  val X_f = mk_nullf (fn (x,y,z) => !x_current)
  val Y_f = mk_nullf (fn (x,y,z) => !y_current)
  val Z_f = mk_nullf (fn (x,y,z) => !z_current) 
  val suc_f = mk_unf (fn x => x + 1)
  val pred_f = mk_unf (fn x => x - 1)
  val addi_f = mk_binf 1 (op +)
  val diff_f = mk_binf 1 (op -)
  val mult_f = mk_binf 1 (op *)
  val divi_f = mk_binf 5 (op div)
  val modu_f = mk_binf 5 (op mod)
  fun cond_f_aux (a,b,c) = if a <= azero then b else c
  val cond_f = mk_ternf cond_f_aux
  fun array_f_aux a = 
    if a < azero orelse a >= fromInt (Vector.length (!array_glob)) 
    then azero
    else Vector.sub (!array_glob, toInt a)
  val array_f = mk_unf array_f_aux
  val seq_f = array_f
  fun perm_f_aux a = 
    let val modn = fromInt (Vector.length (!array_glob)) in
      Vector.sub (!array_glob, toInt (a mod modn))
    end
  val perm_f = mk_unf perm_f_aux
  fun arr1_f_aux a =  
    Vector.sub (!arr1_glob, toInt (a mod fromInt (Vector.length (!arr1_glob))))
  val arr1_f = mk_unf arr1_f_aux 
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
       val input = IntInf.toInt (f2 x) handle Overflow => raise Div 
       val (y,cost) = f1' input
     in
       testcache cost y
     end)
  end
  | _ => raise ERR "compr_f" ""
  
local open IntInf in
  fun compr_f_aux_nc x f n0 n =
     if f (x, azero, azero) <= azero then 
       (if n0 >= n then x else compr_f_aux_nc (x+aone) f (n0+aone) n)
    else compr_f_aux_nc (x+aone) f n0 n
  fun compr_f_aux2_nc (f,n) = compr_f_aux_nc azero f azero n
  val compr_f_nc = mk_binf1 compr_f_aux2_nc
end

val execv = 
  if !array_flag then Vector.fromList
    [zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,
     cond_f,x_f,y_f,array_f,assign_f,loop_f]
  else if !minimal_flag 
    then Vector.fromList [zero_f, x_f, y_f, suc_f, pred_f, loop_f]
  else
    Vector.fromList 
    ([zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,
     cond_f,loop_f,x_f,y_f,
     if !fs_flag orelse !pgen_flag then compr_f_nc else compr_f, 
     loop2_f] @
     (if !z_flag then [z_f, loop3_f] else []) @
     (if !extranum_flag then 
      [three_f, four_f, five_f, six_f, seven_f, eight_f, nine_f, ten_f] 
      else []) @
     (if !fs_flag then [perm_f] else []) @
     (if !pgen_flag then [seq_f] else [])
     )
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
    fn (x,y,z) =>
    if large_int x orelse y <> azero orelse z <> azero then exec (x,y,z) else  
    let val n = IntInf.toInt x in
      if n = Vector.length v andalso !abstimer + b > !timelimit
        then raise ProgTimeout 
      else 
      if n >= 0 andalso n < Vector.length v then 
        let val (r,tim) = Vector.sub (v,n) in
          testcache tim r
        end
      else exec (x,y,z)   
    end
  end
 
fun create_fsf exec =  
  let    
    fun h permlen i = 
      let open IntInf in
        exec (fromInt i, fromInt permlen, azero) mod fromInt permlen
      end
    fun g x =     
      let 
        val perm = Vector.sub (perminputv, IntInf.toInt x)
        val _ = array_glob := Vector.fromList (map IntInf.fromInt perm)
        val permlen = length perm
        val newperm = List.tabulate (permlen,
          fn i => IntInf.toInt (h permlen i))
      in 
        case dfindo newperm permd of 
          NONE => IntInf.fromInt (~1)
        | SOME permi => IntInf.fromInt permi
      end
  in
    g
  end
     
fun coverf_oeis exec = 
  if !fs_flag then cover_oeis (create_fsf exec) else
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

fun mk_exec_zerov p = 
  let val f = mk_exec p in (fn x => f (azero , azero, azero)) end

fun mk_exec_onev p = 
  let val f = mk_exec p in (fn x => f (x, azero, azero)) end
  
fun mk_exec_twov p = 
  let val f = mk_exec p in (fn (x,y) => f (x, y, azero)) end  
  
fun coverp_target p target = cover_target (mk_exec_onev p) target

(* -------------------------------------------------------------------------
   Program generating program.
   Generate a sequence of instructions modulo (maxmove + 1) until
   the stop token maxmove 
   ------------------------------------------------------------------------- *)

val pgen_limit = 100

fun penum_pgenf f target = 
  let
    val _ = init_timer ()
    val _ = array_glob := Vector.fromList target
    val l = ref []
    fun loop i x = 
      if i >= pgen_limit then raise Div else 
      if not (null (!l)) andalso hd (!l) = maxmove then () else
      (
      l := IntInf.toInt (IntInf.mod (f x, IntInf.fromInt (maxmove + 1))) :: !l; 
      incr_timer ();
      loop (i+1) (aincr x)
      )
    val _ = catch_perror (loop 0) azero (fn () => ())
    val po =  
      if not (not (null (!l)) andalso hd (!l) = maxmove) 
      then SOME (prog_of_movel (rev (tl (!l)))) handle HOL_ERR _ => NONE
      else NONE
  in  
    case po of NONE => false | SOME p => fst (coverp_target p target)
  end
  
fun penum_pgen p = 
  let 
    val _ = init_fast_test ()
    val l = ref []
    val f = mk_exec_zerov p
    fun g (anum,target) = 
      if penum_pgenf f target then l := anum :: !l else ()
  in 
    app g []
  end
  
(* -------------------------------------------------------------------------
   Sequences generated by a program up to a number n.
   ------------------------------------------------------------------------- *)

fun penum2_list p ltop =
  let 
    val _ = init_slow_test ()
    val f = mk_exec_twov p
    val _ = init_timer ()
    val l = ref []
    fun loop lloc = 
      case lloc of [] => () | (x,y) :: m =>  
      (l := f (x,y) :: !l; incr_timer (); loop m)
  in  
    loop ltop;
    rev (!l)
  end

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
    if length seq1 <> n orelse length seq2 <> n
    then (is_prefix seq2 seq1 orelse is_prefix seq1 seq2, false)
    else (seq1 = seq2, true)
  end


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


     
