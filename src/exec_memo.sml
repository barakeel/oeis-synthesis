structure exec_memo :> exec_memo =
struct

open HolKernel boolLib aiLib kernel bloom
val ERR = mk_HOL_ERR "exec_memo"
type prog = kernel.prog
type exec = IntInf.int list * IntInf.int list -> IntInf.int list


(* load "kernel"; open kernel aiLib; *)

(* -------------------------------------------------------------------------
   Mark constants programs with true (does not support z)
   ------------------------------------------------------------------------- *)

datatype progb = Insb of (id * bool * progb list);

fun is_const (Insb (_,b,_)) = b

fun mk_progb (Ins (id,pl)) = 
  if null pl then 
    if id = x_id orelse id = y_id 
    then (Insb (id,false,[])) 
    else (Insb (id,true,[]))
  else
  let 
    val newpl = map mk_progb pl
    val hari = Vector.sub (ho_ariv,id) 
  in
    if hari = 0 
    then Insb (id, all is_const newpl, newpl)
    else Insb (id, all is_const (snd (part_n hari newpl)), newpl)
  end

(* -------------------------------------------------------------------------
   Memory reused across different programs to avoid unnecessary reallocation.
   ------------------------------------------------------------------------- *)

val meml_free = ref []
val meml_used = ref []

fun get_mem () = case !meml_free of
    [] =>
    let val a = Array.array (memo_number,0) in
      meml_used := a :: !meml_used;
      a
    end
  | a :: m => (meml_free := m; meml_used := a :: !meml_used; a)
     
fun reset_mem () =
  (
  meml_free := (!meml_used) @ (!meml_free);
  meml_used := []
  )

fun store_mem ((mema,memn),n,x) = (Array.update (a,n,x); memn := n + 1)

(* -------------------------------------------------------------------------
   Time limit wrappers
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

fun checktimer y = 
  (
  incr abstimer;
  if !abstimer > !timelimit then raise ProgTimeout else y
  )
  
fun cost costn x = 
  if large_int x then IntInf.log2 (IntInf.abs x) else costn
    
fun checktimerc costn y =
  (
  abstimer := !abstimer + cost costn (hd y);
  if !abstimer > !timelimit then raise ProgTimeout else y
  )

(* -------------------------------------------------------------------------
   Time limit wrappers
   ------------------------------------------------------------------------- *)

fun mk_nullf opf fl = case fl of
   [] => (fn x => checktimer (opf x))
  | _ => raise ERR "mk_nullf" ""

fun mk_binf costn opf fl = case fl of
   [f1,f2] => (fn x => checktimerc costn (opf (f1 x, f2 x)))
  | _ => raise ERR "mk_binf" ""

fun mk_ternf opf fl = case fl of
   [f1,f2,f3] => (fn x => checktimer (opf (f1 x, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf" ""

fun mk_ternf1 opf fl = case fl of
   [f1,f2,f3] => (fn x => checktimer (opf (f1, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf1" ""

fun mk_quintf2 opf fl = case fl of
   [f1,f2,f3,f4,f5] => (fn x => checktimer (opf (f1, f2, f3 x, f4 x, f5 x)))
  | _ => raise ERR "mk_quintf2" ""

(* -------------------------------------------------------------------------
   Basic intructions
   ------------------------------------------------------------------------- *)
 
val zero_f = mk_nullf (fn (x,y) => [azero])
val one_f = mk_nullf (fn (x,y) => [aone])
val two_f = mk_nullf (fn (x,y) => [atwo])
val x_f = mk_nullf (fn (x,y) => x)
val y_f = mk_nullf (fn (x,y) => y)

fun mk_e f (l1,l2) = case (l1,l2) of
    ([],_) => raise Empty
  | (_,[]) => raise Empty
  | (a1 :: m1, a2 :: m2) => (f (a1,a2) :: m1)
  
val addi_f = mk_binf 1 (mk_e (op +))
val diff_f = mk_binf 1 (mk_e (op -))
val mult_f = mk_binf 1 (mk_e (op *))
val divi_f = mk_binf 5 (mk_e (op div))
val modu_f = mk_binf 5 (mk_e (op mod))

fun cond_f fl = case fl of
    [f1,f2,f3] => 
    (fn x => checktimer (if hd (f1 x) <= azero then f2 x else f3 x))
  | _ => raise ERR "mk_condf" ""

fun push_f fl = case fl of
    [f1,f2] => 
    (fn x => checktimer (hd (f1 x) :: (f2 x))
  | _ => raise ERR "mk_pushf" ""

fun pop_f fl = case fl of
   [f] => 
   (
   fn x => 
     let val y = case f x of [] => raise Empty | [a] => [a] | a :: m => m in
       checktimer y
     end
   )
  | _ => raise ERR "mk_popf" ""

(* -------------------------------------------------------------------------
   Loop with memory
   ------------------------------------------------------------------------- *)

fun helperm_loop mem f1 f2 n ncur x1 x2 = 
  if ncur >= n then x1 else
  let 
    val (newx1,newx2) = (f1 (x1,x2),f2 (x1,x2)) 
    val newncur = ncur + 1
  in
    store_mem (mem,newncur,(newx1,newx2));
    helperm_loop f1 f2 n newncur newx1 newx2
  end
 
fun helperm (mema,memn) f1 f2 n x1 x2 =
  if n < !memn then Array.sub (mema,n) else
  if !memn <= 0 then 
    (store_mem ((mema,memn),0,(x1,x2));
     helperm_loop (mema,memn) f1 f2 n 0 x1 x2)
  else
  let 
    val lastn = !memn - 1
    val (newx1,newx2) = Array.sub (mema,lastn) 
  in
    helperm_loop (mema,memn) f1 f2 n lastn newx1 newx2
  end

fun loop2m_f_aux () = 
  let 
    val mema = get_mem ()
    val memn = ref 0
  in 
    fn (f1,f2,n,x1,x2) => helperm mem f1 f2 (IntInf.toInt (hd n)) x1 x2
  end

val loop2m_f = mk_quintf2 (loop2m_f_aux ())

fun loopm_f_aux () =
  let 
    val mema = get_mem ()
    val memn = ref 0
    fun f2 (x1,x2) = [aincr (hd x2)]
  in
    fn (f1,n,x1) => helperm f1 f2 (IntInf.toInt (hd n)) x1 [aone]
  end
  
val loopm_f = mk_ternf1 loopm_f_aux

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

(* -------------------------------------------------------------------------
   Comprehension
   ------------------------------------------------------------------------- *)

(* find the next element satisfying f starting at x *)
fun compr_next f x =
  if hd (f (x,[azero])) <= azero then x else 
  compr_next f [aincr (hd x)]

(* i and x starts at -1 *)           
fun compr_loop mem f n i x =
  if i >= n then x else 
  let 
    val newx = compr_next f (x+1) 
    val newi = i+1
  in
    store_mem (mem,newi,(newx,[])); compr_loop f n newi newx
  end
         
fun compr_wrap f =
  let
    val mema = get_mem ()
    val memn = ref 0
    fun newf n =
      if n < !memn then Array.sub (mema,n) else 
      if !memn <= 0 then compr_loop (mema,memn) f n (~1) (~1) else
      let 
        val i = !memn - 1
        val x = fst (Array.sub (mema,i)) 
      in
        compr_loop (mema,memn) f n i x
      end
  in
    newf
  end

fun compr_f fl = case fl of
    [f1,f2] =>
    let val f1' = compr_wrap f1 in
      (
      fn x =>
      let val y = f1' (IntInf.toInt (hd (f2 x))) in
        checktimer y
      end
      )
    end
  | _ => raise ERR "compr_f" ""


(* -------------------------------------------------------------------------
   Instruction sets
   ------------------------------------------------------------------------- *)

val org_execl = 
  [zero_f, one_f, two_f, addi_f, diff_f, mult_f, divi_f, modu_f, cond_f,
   loop_f, x_f, y_f, compr_f, loop2_f]

val execv = Vector.fromList (org_execl @ [push_f, pop_f])

(* -------------------------------------------------------------------------
   Creates executable for a program
   ------------------------------------------------------------------------- *)

fun wrap_const f =
  let 
    val bref = ref false
    val yref = ref azero
    fun newf x =  
      if !bref then checktimer (!yref) else 
      let val y = f x in bref := true; yref := y; y end
  in
    newf
  end

fun wrap_loop p id fl = case p of
    Insb (9,b,[p1,p2,p3]) => 
    if not b andalso is_const p3 
    then loopm_f fl
    else Vector.sub (execv,id) fl
  | Insb (13,b,[p1,p2,p3,p4,p5]) =>
    if not b andalso is_const p4 andalso snd_prog p5 
    then loop2m_f fl
    else Vector.sub (execv,id) fl
  | _ => Vector.sub (execv,id) fl
  
fun mk_exec_loop (p as (Insb (id,b,pl))) = 
  let 
    val fl = map mk_exec_loop pl 
    val f1 = wrap_loop p id fl
    val f2 = if b then wrap_const f1 else f1
  in 
    f2
  end
  
fun mk_exec p = 
  let
    val p' = mk_progb p

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
  self = "exec_memo.execspec",
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
load "exec_memo"; open aiLib kernel exec_memo;
parallel_exec 60 "lmfdb3";
*)  




end (* struct *)


(* -------------------------------------------------------------------------
   Verifying that new code accept old solutions
   ------------------------------------------------------------------------- *)

(*
PolyML.print_depth 10;
load "exec_memo";  open kernel aiLib exec_memo;

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


     
