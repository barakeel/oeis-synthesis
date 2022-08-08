(* ========================================================================== *)
(* This file shows how to replicate the figures and tables in the paper       *)
(* "Learning Program Synthesis for Integer Sequences from Scratch"            *)
(* ========================================================================== *)

(* --------------------------------------------------------------------------
   Number y of OEIS sequences with length x
   -------------------------------------------------------------------------- *)

load "bloom"; open aiLib bloom;

fun array_to_list v = Array.foldr (op ::) [] v;
val seql = List.mapPartial I (array_to_list oseq);
val lend = count_dict (dempty Int.compare) (map length seql);
fun f (i,j) = its i ^ " " ^ its j;
writel "length-distrib" (map f (dlist lend));

(* --------------------------------------------------------------------------
   Side experiments. 
   The de-anonymized repository containing the required commits will be made 
   available in the final version before publication.
   Table created by grepping respective exp/expname/log files.
   -------------------------------------------------------------------------- *)

(* noise experiment: switch to commit 
  28b76dcd3376115cbbc327fe59a7a82eb74a40d8z *)

load "rl"; open rl;
maxgen := SOME 4;
expname := "e-noise1";
rl_search "_main" 0;
expname := "e-noise2";
rl_search "_main" 0;
expname := "e-noise3";
rl_search "_main" 0;

(* random target experiment: switch to commit   
   018eeda6228ce0343d530b18b531e80e7b4be033 *)

load "rl"; open rl;
expname := "e-noise1";
rl_search "_main" 0;

(* --------------------------------------------------------------------------
   Full-scale self-learning run.
   Table and figure created by grepping exp/full-scale/log for "solutions:".
   -------------------------------------------------------------------------- *)

load "rl"; open rl;
expname := "full-scale";
rl_search "_main" 0;

(* --------------------------------------------------------------------------
   Number of solutions with size x
   -------------------------------------------------------------------------- *)

load "kernel"; open aiLib kernel;
val iprogl = read_iprogl "model/isol25";
val progl = map snd iprogl;

val sizel = map prog_size (mk_fast_set prog_compare progl);
val sizel2  = dlist (count_dict (dempty Int.compare) sizel);
writel "size-distrib" (map (fn (a,b) => its a ^ " " ^ its b) sizel2);


(* --------------------------------------------------------------------------
   Generalization to larger inputs
   Switch to commit 
   -------------------------------------------------------------------------- *)

load "kernel"; open kernel;
load "aiLib" ; open aiLib;

val ERR = mk_HOL_ERR "test";
val dir = "/home/thibault/big/datasets/oeis-bfile";

fun readln ntop path =
  let
    val file = TextIO.openIn path
    fun loop n file = if n <= 0 then [] else 
      (case TextIO.inputLine file of
        SOME line => line :: loop (n-1) file
      | NONE => [])
    val l1 = loop ntop file
    fun rm_last_char s = String.substring (s,0,String.size s - 1)
    fun is_empty s = s = ""
    val l2 = map rm_last_char l1 (* removing end line *)
    val l3 = filter (not o is_empty) l2
  in
    (TextIO.closeIn file; l3)
  end;

val isol25 = read_iprogl 
  "/home/thibault/big/save/oeis-dev.old/exp/run312/isol25";
length isol25;

fun get_seq_sl sl =
  let fun f s = 
    if all Char.isSpace (explode s) orelse 
       String.isPrefix "#" s 
    then NONE else
    let val (s1,s2) = pair_of_list 
      (first_n 2 (String.tokens Char.isSpace s))         
    in
      if String.size s2 > 285 then NONE else
      SOME (valOf (IntInf.fromString s1), valOf (IntInf.fromString s2)) 
    end
  in
    List.mapPartial f sl
  end;
  
val counter = ref 0  
fun get_seq (i,p) =
  let val file = dir ^ "/b" ^ its i ^ ".txt" in
    incr counter;
    if !counter mod 1000 = 0 then print "." else ();
    if longfile file 
    then SOME ((i,p), get_seq_sl (readln 300 file))
    else NONE
  end;
  
val isol25e = List.mapPartial get_seq isol25;
length isol25e;

fun in_order l = seq_compare
    (map fst l, List.tabulate (length l, IntInf.fromInt)) = EQUAL

load "bloom"; open bloom;
fun is_prefix_alt ((i,p),l) = 
  let 
    val seq1 = valOf (Array.sub (oseq,i)) 
    val seq2 = map snd l
  in
    is_prefix seq1 seq2
  end;

val maxnext = 100;
fun continuous l = case l of
    [] => true
  | [a] => true
  | a :: b :: m => b = IntInf.+ (a, IntInf.fromInt 1) andalso 
                   continuous (b :: m);

fun is_continuous ((i,p),l) = 
  let val seq1 = valOf (Array.sub (oseq,i)) in
    continuous (map fst (first_n (length seq1 + maxnext) l))
  end;
  
fun is_continuous ((i,p),l) = 
  let val seq1 = valOf (Array.sub (oseq,i)) in
    continuous (map fst (first_n (length seq1 + maxnext) l))
  end;
  
fun keep_ext ((i,p),l) = 
  let val seq1 = valOf (Array.sub (oseq,i)) in
    if length l < length seq1 + maxnext
    then NONE
    else SOME ((i,p), map snd (first_n (length seq1 + maxnext) l))
  end; 

load "exec"; open exec;
counter := 0;
fun is_correct ((i,p),l) = 
  let val l' = penum_wtime 10000000 p (length l) in
    seq_compare (l',l) = EQUAL
  end;
  
fun is_timeout ((i,p),l) = 
  let val l' = penum_wtime 10000000 p (length l) in
    length l' < length l
  end;  

fun correct_bl ((i,p),l) = 
  let 
    val seq1 = valOf (Array.sub (oseq,i))
    val i1 = length seq1
    val l' = penum_wtime 10000000 p (length l)
  in
    ((i,p), List.tabulate (maxnext, fn x => 
       seq_compare (first_n (i1+x+1) l', first_n (i1+x+1) l) = EQUAL))
  end;  

PolyML.print_depth 1;
val l0 = filter is_prefix_alt isol25e; length l0;
val l1 = filter is_continuous l0; length l1;
val l2 = List.mapPartial keep_ext l1; length l2;

val l3 = filter is_correct l2; length l3;
val l4 = filter (not o is_timeout) l2; length l4;
val l5 = map correct_bl l2; length l5;
val l6 = list_combine (map snd l5);
val l7 = map (fn l => sum_int (map (fn x => if x then 1 else 0) l)) l6;
val l8 = map (fn x => int_div x (length l5)) l7;
fun f (i,x) = print_endline (its i ^ " " ^ rts x); 

app f (number_fst 0 (1.0 :: l8));   
length l2;
length l2 - length l4;
length l3;



(* 
load "kernel"; open kernel aiLib;
load "human"; open human;

(* identifiers *)
val zero_id = 0
val one_id = 1
val two_id = 2
val addi_id = 3
val diff_id = 4
val mult_id = 5
val divi_id = 6
val modu_id = 7
val cond_id = 8
val loop_id = 9
val x_id = 10
val y_id = 11
val compr_id = 12
val loop2_id = 13

(* reading solutions from the corresponding generation *)




(* distribution of sizes *)


(* diff *)
val predd = enew prog_compare (map snd (read_iprogl "isol17"));
val diffl = filter (fn x => not (emem (snd x) predd)) iprogl;
(* writel "diff" (map string_of_iprog (dict_sort (snd_compare prog_compare_size) diffl)); *)
val diffl2 = dict_sort (snd_compare prog_compare_size) diffl;
val (an,p) = hd diffl;
humanf p; prog_size p;

(* nested levels *)
fun nested_level (Ins (id,pl)) =
  if mem id [compr_id,loop2_id,loop_id] 
  then 1 + (if null pl then 0 else list_imax (map nested_level pl))
  else (if null pl then 0 else list_imax (map nested_level pl));

val l1 = map_assoc (fn (_,p) => nested_level p) iprogl;
val l2 = dict_sort compare_imax l1;
hd l2;
val l3 = map fst (filter (fn x => snd x = 6) l2);
val (i,p) = hd l3;
humanf p; i;

(* longest program *)
val l1 = map_assoc (prog_size o snd) iprogl;
val l2 = dict_sort compare_imax l1;
val ((an,p),i) = hd l2;
humanf p; an; i;

val test =
((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((
0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
324



fun is_constant p = not (depend_on_x p) andalso not (depend_on_y p);
val constl = filter (is_constant o fst) prognl2;
app print_endline (map humanif constl);

load "exec"; open exec;
rt_glob := Timer.startRealTimer (); 
timelimit := 100.0;
val constel = map_assoc (fn (p,i) => mk_exec p (IntInf.zero,IntInf.zero)) constl; 

val largel = first_n 3 (rev (dict_sort (snd_compare IntInf.compare) constel));
fun humanrif ((p,i),r) = IntInf.toString r ^ ": " ^ its i ^ ": " ^ humanf p;
app print_endline (map humanrif largel);
(*
8916100448256i: 1: loop(\(x,y).loop(\(x,y).(loop(\(x,y).((x * 2) + x) - 2, 2, 2) + 2) * x, x, 1), 2, 1)
285311670611i: 1: loop(\(x,y).loop(\(x,y).(((1 + 2) + 2) * (x * 2)) + x, x, 1), 2, 1)
10000000000i: 1: loop(\(x,y).loop(\(x,y).((2 * (2 + 2)) + 2) * x, x, 1), 2, 1)
*)

fun is_xpoly (Ins (id,progl)) =
  if mem id [zero_id,one_id,two_id,x_id,y_id,addi_id,mult_id,diff_id] 
  then all is_xpoly progl 
  else false

val xpolyl = filter (fn (p,_) => is_xpoly p andalso not (is_constant p)) prognl2;
app print_endline (first_n 100 (map humanif xpolyl));


fun is_loop (Ins (id,progl)) = id = loop_id;
val xpolyl = filter (is_loop o fst) prognl2;
app print_endline (first_n 100 (map humanif xpolyl));

fun is_loop (Ins (id,progl)) = id = loop2_id;
val xpolyl = filter (is_loop o fst) prognl2;
app print_endline (first_n 10 (map humanif xpolyl));


val p1 = fst (List.nth (prognl2, 14));
val p2 = fst (List.nth (prognl2, 27));
prog_compare_size (p1,p2);

fun is_test (Ins (id,progl)) = id = cond_id;
val l1 = filter (is_test o fst) prognl2;
val l2 = map (fn (Ins (_,l),i) => (hd l,i)) l1;
val l3 = dlist (dsum prog_compare l2);
val l4 = dict_sort compare_imax l3;

app print_endline (first_n 10 (map humanif l4));

fun is_loop (Ins (id,progl)) = id = compr_id;
val xpolyl = filter (is_loop o fst) prognl2;
app print_endline (first_n 100 (map humanif xpolyl));

(* the number of unique sequence after restrictions *)
load "bloom"; open bloom aiLib kernel;
val l = List.mapPartial I (array_to_list oseq);

local open IntInf in
  fun arb_pow a b = if b <= zero then one else a * arb_pow a (b-one)
  val maxarb = arb_pow (fromInt 10) (fromInt 6)
  val minarb = ~maxarb
  fun reduce x = if x > maxarb then maxarb + one else 
                 if x < minarb then minarb - one else x
end ;

val l1 = map (map reduce o (first_n 16)) l;
val d = count_dict (dempty seq_compare) l1;

val l2 = filter (fn x => snd x = 1) (dlist d);
length l2;

