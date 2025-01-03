structure exec_wrat :> exec_wrat =
struct

open HolKernel boolLib aiLib kernel bloom exec_prim
val ERR = mk_HOL_ERR "exec_wrat"
type prog = kernel.prog
type rat = exec_prim.rat
type exec = rat list * rat list -> rat list

local open IntInf in
  val azero = fromInt 0
  val aone = fromInt 1
  val atwo = fromInt 2
  fun aincr x = x + aone
  fun adecr x = x - aone
  val maxint = fromInt (valOf (Int.maxInt))
  val minint = fromInt (valOf (Int.minInt))
  fun large_int x = x > maxint orelse x < minint
end

(* -------------------------------------------------------------------------
   Mark constants programs with true
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
   Memory
   ------------------------------------------------------------------------- *)

val rldefault = rlzero 
val default_entry = (rldefault, rldefault)

fun get_mem () = ref (Array.array (16, default_entry))

fun resize_array a n = 
  let val dest = Array.array (2 * n, default_entry) in
    Array.copy {src = !a, dst = dest, di = 0};
    a := dest
  end

fun store_mem ((mema,memn),n,x) = 
  if n >= memo_number then () else
  let val meman = Array.length (!mema) in
    if n >= meman then resize_array mema meman else ();
    Array.update (!mema,n,x); 
    memn := n + 1
  end
  handle Subscript => raise ERR "store_mem" (its n)

fun lookup_mema (mema,n) = Array.sub (!mema,n) 
  handle Subscript => raise ERR "lookup_mema" (its n)

(* -------------------------------------------------------------------------
   Wrappers
   ------------------------------------------------------------------------- *)

fun mk_nullf opf fl = case fl of
    [] => (fn x => (opf x))
  | _ => raise ERR "mk_nullf" ""

fun mk_unf opf fl = case fl of
    [f] => (fn x => 
    let val t = f x in
      case t of x1 :: m => opf x1 :: m | _ => raise Empty
    end
    )
  | _ => raise ERR "mk_binfadd" ""

fun mk_binf opf fl = case fl of
    [f1,f2] => (fn x => 
    let 
      val (t1,t2) = (f1 x,f2 x)
      val x2 = hd t2
    in
      case t1 of x1 :: m => (opf x1 x2) :: m | _ => raise Empty
    end
    )
  | _ => raise ERR "mk_binfadd" ""

fun mk_ternf1 opf fl = case fl of
    [f1,f2,f3] => 
    (fn x => (checktimer (); opf (f1, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf1" ""

fun mk_quintf2 opf fl = case fl of
    [f1,f2,f3,f4,f5] => 
    (fn x => (checktimer (); opf (f1, f2, f3 x, f4 x, f5 x)))
  | _ => raise ERR "mk_quintf2" ""

fun mk_quintf3 opf fl = case fl of
    [f1,f2,f3,f4,f5] => 
    (fn x => (checktimer (); opf (f1, f2, f3, f4 x, f5 x)))
  | _ => raise ERR "mk_quintf3" ""

(* -------------------------------------------------------------------------
   Basic intructions
   ------------------------------------------------------------------------- *)

val zero_f = mk_nullf (fn (x,y) => [rzero ()])
val one_f = mk_nullf (fn (x,y) => [rone ()])
val two_f = mk_nullf (fn (x,y) => [rtwo ()])
val x_f = mk_nullf (fn (x,y) => (checktimer (); x))
val y_f = mk_nullf (fn (x,y) => (checktimer (); y))

val addi_f = mk_binf raddi
val diff_f = mk_binf rdiff
val mult_f = mk_binf rmult
val divi_f = mk_binf rdivi
val modu_f = mk_binf rmodu

fun cond_f fl = case fl of
    [f1,f2,f3] => 
    (fn x => (checktimer (); if rleq0 (hd (f1 x)) then f2 x else f3 x))
  | _ => raise ERR "cond_f" ""
  
(* -------------------------------------------------------------------------
   List instructions
   ------------------------------------------------------------------------- *)  
   
fun push_f fl = case fl of
    [f1,f2] => (fn x => pushl (f1 x) (f2 x))
  | _ => raise ERR "push_f" ""

fun pop_f fl = case fl of
   [f] => (fn x => popl (f x))
  | _ => raise ERR "pop_f" ""  
 
(* -------------------------------------------------------------------------
   Rational instructions
   ------------------------------------------------------------------------- *) 

val divr_f = mk_binf rdivr
val floor_f = mk_unf rfloor

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
    helperm_loop mem f1 f2 n newncur newx1 newx2
  end
 
fun helperm (mema,memn) f1 f2 n x1 x2 =
  if n < 0 then x1 else 
  if n < !memn then fst (lookup_mema (mema,n)) else
  if !memn <= 0 then 
    (store_mem ((mema,memn),0,(x1,x2));
     helperm_loop (mema,memn) f1 f2 n 0 x1 x2)
  else
  let 
    val lastn = !memn - 1
    val (newx1,newx2) = lookup_mema (mema,lastn) 
  in
    helperm_loop (mema,memn) f1 f2 n lastn newx1 newx2
  end

fun loop2m_f_aux () = 
  let 
    val mema = get_mem ()
    val memn = ref 0
    val mem = (mema,memn)
  in 
    fn (f1,f2,n,x1,x2) => helperm mem f1 f2 (mk_rbound n) x1 x2
  end

fun loop2m_f () = mk_quintf2 (loop2m_f_aux ())

fun loopm_f_aux () =
  let
    val mema = get_mem ()
    val memn = ref 0
    val mem = (mema,memn)
    fun f2 (x1,x2) = rlincr x2
  in
    fn (f1,n,x1) => helperm mem f1 f2 (mk_rbound n) x1 rlone
  end
  
fun loopm_f () = mk_ternf1 (loopm_f_aux ())

(* -------------------------------------------------------------------------
   Loops
   ------------------------------------------------------------------------- *)

fun helper f1 f2 n x1 x2 = 
  if n <= 0 then x1 else helper f1 f2 (n - 1) (f1 (x1,x2)) (f2 (x1,x2))

fun loop2_f_aux (f1,f2,n,x1,x2) = helper f1 f2 (mk_rbound n) x1 x2
val loop2_f = mk_quintf2 loop2_f_aux

fun loop_f_aux (f1,n,x1) = 
  helper f1 (fn (x1,x2) => rlincr x2) (mk_rbound n) x1 rlone
val loop_f = mk_ternf1 loop_f_aux

(* -------------------------------------------------------------------------
   While loop
   ------------------------------------------------------------------------- *)

fun whelper f1 f2 f3 x1 x2 = 
  if fst (hd (f3 (x1,x2))) <= azero then x1 else 
  whelper f1 f2 f3 (f1 (x1,x2)) (f2 (x1,x2))

fun while2_f_aux (f1,f2,f3,x1,x2) = whelper f1 f2 f3 x1 x2
val while2_f = mk_quintf3 while2_f_aux

(* -------------------------------------------------------------------------
   Comprehension
   ------------------------------------------------------------------------- *)

(* find the next element satisfying f starting at x *)
fun compr_next f x =
  if rleq0 (hd (f (x,rlzero))) then x else compr_next f (rlincr x)

(* i and x starts at -1 *)           
fun compr_loop mem f n i x =
  if i >= n then x else 
  let 
    val newx = compr_next f (rlincr x)
    val newi = i+1
  in
    store_mem (mem,newi,(newx,rldefault)); 
    compr_loop mem f n newi newx
  end
   
val comprstart = rlmone
      
fun compr_wrap f =
  let
    val mema = get_mem ()
    val memn = ref 0
    fun newf n =
      if n < 0 then raise Div else
      if n < !memn then fst (Array.sub (!mema,n)) else 
      if !memn <= 0 then compr_loop (mema,memn) f n (~1) comprstart else
      let 
        val i = !memn - 1
        val x = fst (Array.sub (!mema,i)) 
      in
        compr_loop (mema,memn) f n i x
      end
  in
    newf
  end

fun compr_f fl = case fl of
    [f1,f2] =>
    let val f1' = compr_wrap f1 in
      (fn x => (checktimer (); f1' (mk_rbound (f2 x))))
    end
  | _ => raise ERR "compr_f" ""

(* -------------------------------------------------------------------------
   Instruction sets
   ------------------------------------------------------------------------- *)

val org_execl = 
  [zero_f, one_f, two_f, addi_f, diff_f, mult_f, divi_f, modu_f, cond_f,
   loop_f, x_f, y_f, compr_f, loop2_f]

val wrat_execl = [push_f, pop_f, while2_f, divr_f, floor_f]
 
val execv = Vector.fromList (org_execl @ wrat_execl)

val _ = if Vector.length execv <> Vector.length operv andalso (!wrat_flag)
        then raise ERR "execv" "mismatch with operv"
        else () 

(* -------------------------------------------------------------------------
   Creates executable for a program
   ------------------------------------------------------------------------- *)

fun wrap_const f =
  let 
    val bref = ref false
    val yref = ref rldefault
    fun newf x =  
      if !bref then (checktimer (); !yref) else 
      let val y = f x in bref := true; yref := y; y end
  in
    newf
  end

fun wrap_loop p id fl = case p of
    Insb (9,b,[p1,p2,p3]) => 
    if not b andalso is_const p3 
    then (loopm_f ()) fl
    else Vector.sub (execv,id) fl
  | Insb (13,b,[p1,p2,p3,p4,p5]) =>
    if not b andalso is_const p4 andalso is_const p5 
    then (loop2m_f ()) fl
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
  
fun mk_exec p = mk_exec_loop (mk_progb p)
  handle ProgTimeout => raise ERR "mk_exec" (its (!abstimer))

fun mk_rsing x = [((x,1) : rat)]

fun mk_exec_onev p = 
  let val exec = mk_exec p in 
    (fn x => mk_rreturn (exec (mk_rsing x,rlzero)))
  end

fun coverf_oeis exec = 
  let fun g x = mk_rreturn (exec (mk_rsing x,rlzero)) in
    scover_oeis g 
  end

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
      loop (i+1) (x+1)
      )
    val _ = catch_perror (loop 0) (0:IntInf.int) (fn () => ())
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

fun verify_file tim file = 
  let 
    val itsol = read_itprogl file
    val isol = map (fn (x,(_,y)) => (x,y)) (distrib itsol) 
    val _ = print_endline ("solutions: " ^ its (length isol))
    val (bbl,t) = add_time (map_assoc (verify_wtime tim)) isol
    val lbad1 = filter (not o fst o snd) bbl
    val lbad2 = filter (not o snd o snd) bbl
  in 
    print_endline 
      (rts_round 4 t ^ ": " ^ its (length lbad1) ^ " " ^ its (length lbad2));
    map fst lbad1
  end

(* -------------------------------------------------------------------------
   Parallel execution
   ------------------------------------------------------------------------- *)

fun execspec_fun pl =
  let  
    val i = ref 0;
    fun f p = (
      incr i; 
      print_endline (its (!i)); 
      penum_wtime 10000000 p 1000);
  in
    map f pl
  end

val execspec : (unit, prog list, seq list) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "exec_wrat.execspec",
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
load "exec_wrat"; open aiLib kernel exec_wrat;
parallel_exec 60 "lmfdb3";
*)  

end (* struct *)


(* -------------------------------------------------------------------------
   Verifying that new code accept old solutions
   ------------------------------------------------------------------------- *)

(*
PolyML.print_depth 10;
load "human"; open human;
load "exec_wrat";  open kernel aiLib exec_wrat;
val badl = verify_file 1000000 (selfdir ^ "/model/itsol209");
val badl = verify_file 1000000 (selfdir ^ "/exp/intl3/hist/itsol2088");


val itsol = read_itprogl file
val isol = map (fn (x,(_,y)) => (x,y)) (distrib itsol);
val _ = print_endline ("solutions: " ^ its (length isol));

fun get_bad isol = case isol of 
    [] => NONE
  | a :: m => 
    if ((verify_wtime 100000 a; false) handle Option => true)
    then SOME a
    else get_bad m
    
val (anum,p) = valOf (get_bad isol);
val (bbl,t) = add_time (map_assoc (verify_wtime tim)) isol
val lbad1 = filter (not o fst o snd) bbl
val lbad2 = filter (not o snd o snd) bbl

val file = (selfdir ^ "/exp/intl3/hist/itsol2088");
val read_itprogl 
*)

(* -------------------------------------------------------------------------
   Testing
   ------------------------------------------------------------------------- *) 
    
(* 
load "exec_wrat"; open exec_wrat; 
load "human"; open kernel human aiLib;

val p =  parse_human "(loop ( * 2 x) x 1)";
val p = parse_human "(% x 2)";
val p = parse_human "(% (- (loop ( * 2 x) x 1) 2) x) "; 
val p =  parse_human "(loop ( * 2 x) x 1)";
val p = parse_human "(loop ( * x x) x 2)";

val p =  parse_human "(- (loop ( * 2 x) x 1) (loop ( * 2 x) x 1))";
val (anum,p) = hd lbad;
val seq = valOf (Array.sub (bloom.oseq, anum));
humanf p;


val p = parse_human "(loop2 (+ x y) x x 2 1)";

abstimer := 0;
val f = mk_exec_onev p;
f 100;
timeincr := 100000000;
!abstimer;

val (l1,t) = add_time (penum_wtime 1000000 p) (length seq);
!abstimer;
*)  

