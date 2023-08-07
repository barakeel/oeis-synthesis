structure exec :> exec =
struct

open HolKernel boolLib aiLib kernel bloom smlParallel
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
  fun arb_pow a b = if b <= azero then aone else a * arb_pow a (b-aone)
  fun pow2 b = arb_pow atwo (fromInt b)
  val maxarb = arb_pow (fromInt 10) (fromInt maxintsize) (* 4.685 * 10 ^ 284 *)
  val minarb = ~maxarb
  val maxint = fromInt (valOf (Int.maxInt))
  val minint = fromInt (valOf (Int.minInt))
  fun large_arb x = x > maxarb orelse x < minarb
  fun large_int x = x > maxint orelse x < minint
end

fun cost costn x = 
  if large_int x then IntInf.log2 (IntInf.abs x) else costn

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
   Global memory
   ------------------------------------------------------------------------- *)

(* array and turing *)
val array_glob = Array.tabulate (500,fn _ => azero)
val arrayi_glob = ref 0
fun init_array () = app (fn i => Array.update (array_glob, i, azero))
  (List.tabulate (Array.length array_glob, I))

(* fs *)
val vector_glob = ref (Vector.fromList [])

(* pgen *)
val resl_glob = ref []
val resn_glob = ref 0



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

fun cond_f fl = case fl of
   [f1,f2,f3] => 
      (fn x =>
       let 
         val y = if f1 x <= azero then f2 x else f3 x
         val _ = abstimer := !abstimer + 1  
       in
         if !abstimer > !timelimit then raise ProgTimeout else y
       end)
  | _ => raise ERR "mk_condf" ""

(* -------------------------------------------------------------------------
   Basic intructions
   ------------------------------------------------------------------------- *)
 
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
val suc_f = mk_unf (fn x => x + 1)
val pred_f = mk_unf (fn x => x - 1)
val addi_f = mk_binf 1 (op +)
val diff_f = mk_binf 1 (op -)
val mult_f = mk_binf 1 (op *)
val divi_f = mk_binf 5 (op div)
val modu_f = mk_binf 5 (op mod)


(* -------------------------------------------------------------------------
   Thinking tokens
   ------------------------------------------------------------------------- *)

val think1_f = mk_unf (fn x => x)
val think2_f = mk_unf (fn x => x)

(* -------------------------------------------------------------------------
   Memory instructions
   ------------------------------------------------------------------------- *)

(* array *)
fun array_f_aux a = 
  if a < azero orelse a >= IntInf.fromInt (Array.length array_glob) 
  then azero
  else Array.sub (array_glob, IntInf.toInt a)
val array_f = mk_unf array_f_aux
fun assign_f_aux (a,b) =
  (
  if a < azero orelse a >= IntInf.fromInt (Array.length array_glob) then ()
  else Array.update (array_glob, IntInf.toInt a, b);
  azero
  )
val assign_f = mk_binf 1 assign_f_aux

(* fs *)
fun perm_f_aux a = 
  let val modn = IntInf.fromInt (Vector.length (!vector_glob)) in
    Vector.sub (!vector_glob, IntInf.toInt (a mod modn))
  end
val perm_f = mk_unf perm_f_aux

(* pgen *)
val pgen_limit = 240
fun mf i = mk_unf (fn x => 
  (
  incr resn_glob; 
  resl_glob := i :: !resl_glob; 
  if !resn_glob >= pgen_limit then raise Div else x)
  )
val mfl = List.tabulate (length pgen_operl, mf) 
val seq_f = array_f

(* turing *)
val next_f = mk_nullf (fn x => 
  (if !arrayi_glob >= Array.length array_glob - 1 
     then raise Div 
     else incr arrayi_glob; 
   azero))
val prev_f = mk_nullf (fn x => 
  (if !arrayi_glob <= 0 then () else decr arrayi_glob; azero))
val read_f = mk_nullf (fn _ => Array.sub (array_glob, !arrayi_glob))
val write_f = mk_unf (fn x => (Array.sub (array_glob, !arrayi_glob); azero))

(* -------------------------------------------------------------------------
   Loops
   ------------------------------------------------------------------------- *)
   
fun loop3_f_aux f1 f2 f3 n x1 x2 x3 = 
  if n <= azero then x1 else 
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

fun loope_f_aux (f,n) = 
  if n <= azero 
  then azero 
  else (f (azero,azero,azero); loope_f_aux (f, adecr n))
  
val loope_f = mk_binf1 loope_f_aux

(* -------------------------------------------------------------------------
   Comprehension
   ------------------------------------------------------------------------- *)
   
fun create_compr f =
  let
    val _ = init_timer ()
    val l = ref []
    val prevtime = ref 0
    fun loop i x =
      if i >= !max_compr_number then () else
      if f (x, azero, azero) <= azero
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

(* -------------------------------------------------------------------------
   Instruction sets
   ------------------------------------------------------------------------- *)

val org_execl = 
  [zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,cond_f,
   loop_f,x_f,y_f,
   if !fs_flag orelse !pgen_flag then compr_f_nc else compr_f, 
   loop2_f]

val array_execv = Vector.fromList
  [zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,
   cond_f,x_f,y_f,array_f,assign_f,loop_f]

val minimal_execv = Vector.fromList 
  [zero_f, x_f, y_f, suc_f, pred_f, loop_f]

val turing_execv = Vector.fromList 
  [zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,cond_f,
   loope_f,next_f,prev_f,write_f,read_f]
 
val execv = 
  if !array_flag then array_execv
  else if !minimal_flag then minimal_execv 
  else if !turing_flag then turing_execv
  else
    Vector.fromList (
    org_execl @
    (if !z_flag then [z_f, loop3_f] else []) @
    (if !extranum_flag 
    then [three_f, four_f, five_f, six_f, seven_f, eight_f, nine_f, ten_f] 
    else []) @
    (if !fs_flag then [perm_f] else []) @
    (if !pgen_flag then [seq_f] @ mfl else []) @
    (if !think_flag then [think1_f,think2_f] else []) @
    (if !seq_flag then [seq_f] else [])
    )
val _ = if Vector.length execv <> Vector.length operv andalso not (!intl_flag)
        then raise ERR "execv" "mismatch with operv"
        else ()

(* -------------------------------------------------------------------------
   Execute a program
   ------------------------------------------------------------------------- *)

fun mk_exec_move id fl = Vector.sub (execv,id) fl
  
fun mk_exec (p as (Ins (id,pl))) = 
  let val fl = map mk_exec pl in mk_exec_move id fl end
  
(* limited to programs that do not depend on y *)  
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
        val _ = vector_glob := Vector.fromList (map IntInf.fromInt perm)
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

fun match_seq seq (exec : exec) =   
  let
    val _ = init_array ()
    val shortseq = first_n (Int.min (10, length seq div 2)) seq
    val _ = app (fn (i,x) => Array.update (array_glob,i,x))
      (number_fst 0 shortseq)
    fun f x = exec (IntInf.fromInt x, azero, azero)
    val _ = init_timer ()
    val r = ref false
    fun loop seqloc x = case seqloc of [] => r := true | a :: m =>
      let val y = f x in 
        if y = a then (incr_timer (); loop (tl seqloc) ((x:int) + 1)) else ()
      end
    val _ = catch_perror (loop seq) 0 (fn () => ())
  in  
    (!r,!abstimer)
  end  


     
fun coverf_oeis exec =
  if !fs_flag then cover_oeis (create_fsf exec) else
  let
    val _ = if !turing_flag then init_array () else ()
    val _ = graph := []
    val _ = graphb := 0
    val i = ref 0
    fun g x = 
      let
        val _ = 
          if !turing_flag then 
            (arrayi_glob := 0; Array.update (array_glob,0,x))
          else ()
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
   
fun apply_move_err move board =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 <> arity 
    then board
    else Ins (move, rev l1) :: l2
  end

fun apply_movel_err movel board = 
  case movel of [] => board | move :: m => 
  apply_movel_err m (apply_move_err move board)
  
fun penum_pgenf f target = 
  let
    val _ = init_array ()
    val _ = app (fn (i,x) => Array.update (array_glob,i,x))
      (number_fst 0 (
      (first_n (Int.min (10, length target div 2)) target)))
    val _ = resn_glob := 0
    val _ = resl_glob := []
    val _ = init_fast_test ()
    val _ = init_timer ()
    val _ = catch_perror f () (fn () => ())
    val movel = !resl_glob
    val po =
      let 
        val board = apply_movel_err movel []
        val pil = map_assoc prog_size board
      in
        if null pil 
        then NONE 
        else SOME (fst (hd (dict_sort compare_imax pil)))
      end
    val _ = init_fast_test ()
    val _ = init_timer ()
  in  
    case po of NONE => NONE | SOME p => 
      (if fst (coverp_target p target) then SOME p else NONE)
  end

val anuml_itsol209 = 
  if !pgen_flag 
  then dict_sort Int.compare 
    (map fst (read_itprogl (selfdir ^ "/model/itsol209")))
  else []
  
fun penum_pgen exec = 
  let
    val l = ref []
    fun f () = ignore (exec (azero, azero, azero))
    fun g anum = 
      let val target = valOf (Array.sub (oseq,anum)) in
        case penum_pgenf f target of
            SOME newp => l := (anum,newp) :: !l 
          | NONE => ()
      end
  in 
    app g anuml_itsol209; rev (!l)
  end 

(* -------------------------------------------------------------------------
   HER experiment (maybe should be looking at
   the 10 best recommendation according to the tnn)
   Maybe add a stop command to the tnn.
   -------------------------------------------------------------------------*)  
  
fun penum_her exec =   
  let
    val _ = init_slow_test ()
    fun f x = exec (Int.fromInt x, azero, azero)
    val _ = init_timer ()
    val l = ref []
    fun loop i x = if i >= 16 then () else
      (l := f x :: !l; incr_timer (); loop (i+1) (x+1))
    val _ = catch_perror (loop 0) 0 (fn () => ())
  in  
    rev (!l)
  end
  
(* -------------------------------------------------------------------------
   seq experiment
   -------------------------------------------------------------------------*)  
  

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
    fun loop i x = if m <= x orelse i >= n then () else
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

val execspec : (unit, prog list, seq list) extspec =
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
    val (ill,t) = add_time (parmap_queue_extern ncore execspec ()) pll
    val il = List.concat ill
    val pseql = combine (pl,il)
    fun g (p,seq) = its (length seq) ^ ", " ^ 
      gpt_of_prog p ^ ", " ^ string_of_seq seq;
  in
    writel (dir ^ "/log") ["time: " ^ rts t];
    writel (dir ^ "/output") (map g pseql)
  end

(*  
load "exec"; open aiLib kernel exec;
parallel_exec 30 "lmfdb1";
*)  




end (* struct *)




(* -------------------------------------------------------------------------
   Verifying that new code accept old solutions
   ------------------------------------------------------------------------- *)

(*
PolyML.print_depth 10;
load "exec"; open kernel aiLib exec;

val itsol = read_itprogl "model/itsol209"; 
val isol = map (fn (x,(_,y)) => (x,y)) (distrib itsol); 
length isol;

init_slow_test ();
val (bbl,t) = add_time (map_assoc (verify_wtime 100000)) isol;
val lbad1 = filter (not o fst o snd) bbl; length lbad1;
val lbad2 = filter (not o snd o snd) bbl; length lbad2;
val lbad = map fst lbad1;
length lbad1; length lbad2; t;


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

val s = "C C L C G C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N K M E C G C H E";


val prog = prog_of_gpt s;

val (f,t) = aiLib.add_time mk_exec prog;

timeincr := 1000000000000;
max_compr_number := 2000;

val (r,t) 
 = aiLib.add_time f (IntInf.fromInt 1000,IntInf.fromInt 0, IntInf.fromInt 0);

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


     
