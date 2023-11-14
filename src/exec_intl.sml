structure exec_intl :> exec_intl =
struct

open HolKernel boolLib aiLib kernel bloom
val ERR = mk_HOL_ERR "exec_intl"
type prog = kernel.prog
type exec = IntInf.int list * IntInf.int list -> IntInf.int list

(* -------------------------------------------------------------------------
   Time limit
   ------------------------------------------------------------------------- *)

local open IntInf in
  val azero = fromInt 0
  val aone = fromInt 1
  val atwo = fromInt 2
  fun aincr x = x + aone
  fun adecr x = x - aone
  fun arb_pow a b = if b <= azero then aone else a * arb_pow a (b-aone)
  fun pow2 b = arb_pow atwo (fromInt b)
  val maxint = fromInt (valOf (Int.maxInt))
  val minint = fromInt (valOf (Int.minInt))
  fun large_int x = x > maxint orelse x < minint
end

fun cost costn x = 
  if large_int x then IntInf.log2 (IntInf.abs x) else costn

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
val x_f = mk_nullf (fn (x,y) => x)
val y_f = mk_nullf (fn (x,y) => y)

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


fun push_f fl = case fl of
   [f1,f2] => 
      (fn x =>
        (incr abstimer;
         if !abstimer > !timelimit 
           then raise ProgTimeout else hd (f1 x) :: (f2 x)
        ))
  | _ => raise ERR "mk_pushf" ""

fun pop_f fl = case fl of
   [f] => 
      (fn x =>
       let val _ = incr abstimer in
         if !abstimer > !timelimit then raise ProgTimeout else 
           (case f x of [] => raise Empty | [a] => [a] | a :: m => m)
       end)
  | _ => raise ERR "mk_popf" ""

(* -------------------------------------------------------------------------
   Memory
   ------------------------------------------------------------------------- *)

val edgev_glob = ref (Vector.fromList [])

fun edge_f_aux a = 
  let val modn = IntInf.fromInt (Vector.length (!edgev_glob)) in
    [IntInf.fromInt 
      (!(fst (Vector.sub (!edgev_glob, IntInf.toInt ((hd a) mod modn)))))]
  end
  
val edge_f = mk_unf edge_f_aux

(* -------------------------------------------------------------------------
   Thinking tokens
   ------------------------------------------------------------------------- *)

val think1_f = mk_unf (fn x => x)
val think2_f = mk_unf (fn x => x)

(* -------------------------------------------------------------------------
   Loops
   ------------------------------------------------------------------------- *)
   
fun helper f1 f2 n x1 x2 = 
  if n <= azero then x1 else 
  helper f1 f2 (adecr n) (f1 (x1,x2)) (f2 (x1,x2))

fun loop2_f_aux (f1,f2,n,x1,x2) = helper f1 f2 (hd n) x1 x2
val loop2_f = mk_quintf2 loop2_f_aux

fun loop_f_aux (f1,n,x1) = 
  helper f1 (fn (x1,x2) => [aincr (hd x2)]) (hd n) x1 [aone]
val loop_f = mk_ternf1 loop_f_aux

(* prepared programs can't be reused because they would need to reset compr *)
fun create_compr f =
  let
    val _ = init_timer ()
    val l = ref []
    fun loop i x =
      if i >= !max_compr_number then () else
      if hd (f (x,[azero])) <= azero
      then (
           l := (x,!abstimer) :: !l;
           incr_timer (); 
           loop (i+1) [aincr (hd x)]
           ) 
      else loop i [aincr (hd x)]
    val _ = catch_perror (loop 0) [azero] (fn () => ())
    val v = Vector.fromList (rev (!l))
    val r = ref 0
  in
    (fn x => 
      (
      if x < 0 then raise Div else 
      if x >= Vector.length v then raise ProgTimeout else 
      let val (y,cost) = Vector.sub (v,x) in
        (y, 1 + (if !r > cost then 0 else 
           let val diff = cost - !r in r := cost; diff end)) 
      end
      )
    )
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


local open IntInf in
  fun compr_f_aux_nc x f n0 n =
     if hd (f ([x],[azero])) <= azero 
     then (if n0 >= n then [x] else compr_f_aux_nc (x+aone) f (n0+aone) n)
     else compr_f_aux_nc (x+aone) f n0 n
  fun compr_f_aux2_nc (f,n) = compr_f_aux_nc azero f azero (hd n)
  val compr_f_nc = mk_binf1 compr_f_aux2_nc
end

(* -------------------------------------------------------------------------
   Instruction sets
   ------------------------------------------------------------------------- *)

val org_execl = 
  [zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,cond_f,
   loop_f,x_f,y_f, compr_f, loop2_f]

val ramsey_execl = 
  [zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,cond_f,
   loop_f,x_f,y_f, loop2_f ,push_f, pop_f, edge_f]

val run_f = mk_unf (fn x => x)

val execv = Vector.fromList (
  if !ramsey_flag then ramsey_execl else
  (org_execl @ 
  [push_f, pop_f] @
  (if !think_flag then [think1_f,think2_f] else []) @
  (if !run_flag then List.tabulate (12, fn _ => run_f) else [])
  ))

val _ = if !intl_flag andalso Vector.length execv <> Vector.length operv
        then raise ERR "execv" "mismatch with operv"
        else ()

(* -------------------------------------------------------------------------
   Execute a program
   ------------------------------------------------------------------------- *)

fun mk_exec_move id fl = Vector.sub (execv,id) fl
  
fun mk_exec (p as (Ins (id,pl))) = 
  let val fl = map mk_exec pl in mk_exec_move id fl end

fun coverf_oeis exec = 
  let fun g x = hd (exec ([x], [azero])) in cover_oeis g end

fun mk_exec_onev p = 
  let val f = mk_exec p in (fn x => hd (f ([x],[azero]))) end
  
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


(* -------------------------------------------------------------------------
   Parallel execution
   ------------------------------------------------------------------------- *)

fun execspec_fun pl =
  let  
    val i = ref 0;
    fun f p = (
      max_compr_number := 1000;
      incr i; 
      print_endline (its (!i)); 
      penum_wtime 10000000 p 1000);
  in
    map f pl
  end

val execspec : (unit, prog list, seq list) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "exec.execspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = let fun f () pl = execspec_fun pl in f end,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_progl,
  read_arg = read_progl,
  write_result = write_seql,
  read_result = read_seql
  }

fun parallel_exec ncore expname =
  let  
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = mkDir_err dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val sl = readl (dir ^ "/input")
    val pl = map prog_of_gpt sl
    val pll = cut_n (10*ncore) pl
    val (ill,t) = add_time 
      (smlParallel.parmap_queue_extern ncore execspec ()) pll
    val il = List.concat ill
    val pseql = combine (pl,il)
    fun g (p,seq) = its (length seq) ^ ", " ^ 
      gpt_of_prog p ^ ", " ^ string_of_seq seq;
  in
    writel (dir ^ "/log") ["time: " ^ rts t];
    writel (dir ^ "/output") (map g pseql)
  end

(*  
load "exec_intl"; open aiLib kernel exec_intl;
parallel_exec 60 "lmfdb3";
*)  




end (* struct *)


(* -------------------------------------------------------------------------
   Verifying that new code accept old solutions
   ------------------------------------------------------------------------- *)

(*
PolyML.print_depth 10;
load "exec_intl";  open kernel aiLib exec_intl;

val itsol = read_itprogl "model/itsol209"; 
val isol = map (fn (x,(_,y)) => (x,y)) (distrib itsol); 
length isol;

init_slow_test ();
val (bbl,t) = add_time (map_assoc (verify_wtime 100000)) isol;
val lbad1 = filter (not o fst o snd) bbl; length lbad1;
val lbad2 = filter (not o snd o snd) bbl; length lbad2;
val lbad = map fst lbad1;
length lbad1; length lbad2; t;

val newisol = filter (fn x => mem x lbad) isol;
val (bbl,t) = add_time (map_assoc (verify_wtime 1000000)) newisol;
val lbad1 = filter (not o fst o snd) bbl; length lbad1;
val lbad2 = filter (not o snd o snd) bbl; length lbad2;
val lbad = map fst lbad1;
length lbad; length lbad2; t;




fun f (i,p) = its i ^ ": " ^ humanf p;
map f lbad;
write_iprogl "lbad" lbad;
val lbad = read_iprogl "lbad";
*)

(* -------------------------------------------------------------------------
   Testinglength lbad2;
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


     
