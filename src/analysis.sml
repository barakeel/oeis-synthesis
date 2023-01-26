(* ========================================================================== *)
(* This file shows how to replicate the figures and tables in the paper       *)
(* "Learning Program Synthesis for Integer Sequences from Scratch"            *)
(* ========================================================================== *)

(* 
 Not that this file assumes by default that the commit used is
 the top of the anonymous repository corresponding to commit
 f227c2f746327e9910df6f64d802aadc7752984f in our main de-anonymized repository.
 Some of the experiments requires commits from our main repository. 
 The address of the main repository will be included in the final version 
 before publication. 
 *)

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
   Table created by grepping respective exp/expname/log files for "solutions:"
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
   Switch to commit 3e67eda98b11275a94ea7e7f9ecde3cf25fbb85b
   Requires to have downloaded b-files in home/user/oeis-bfile
   -------------------------------------------------------------------------- *)

load "kernel"; open aiLib kernel;
load "bloom"; open bloom;
load "exec"; open exec;

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

val isol25 = read_iprogl "model/isol25"; length isol25;
val sol189 = read_itprogl "model/sol189"; length sol189;

fun is_faster (t1,p1) (t2,p2) =   
  cpl_compare Int.compare prog_compare_size ((t1,p1),(t2,p2)) = LESS

fun is_smaller (t1,p1) (t2,p2) = 
  prog_compare_size (p1,p2) = LESS

fun find_min_loop cmpf a m = case m of
    [] => a
  | a' :: m' => find_min_loop cmpf (if cmpf a' a then a' else a)  m'

fun find_min cmpf l = case l of 
    [] => raise ERR "find_min" ""
  | a :: m => find_min_loop cmpf a m

fun fsmall (a,tpl) = (a, snd (find_min is_smaller tpl));
fun ffast (a,tpl) = (a, snd (find_min is_faster tpl));

val smallsol = map fsmall sol189;
val fastsol = map ffast sol189;

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
    SOME ((i,p), get_seq_sl (readln 300 file)) handle _ => NONE
  end;

(* Reads the first 300 lines of each b-file *)  
val sol = fastsol; (* fastsol *)

val sole = List.mapPartial get_seq sol; length sole;



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

  
fun keep_ext ((i,p),l) = 
  let val seq1 = valOf (Array.sub (oseq,i)) in
    if length l < length seq1 + maxnext
    then NONE
    else SOME ((i,p), map snd (first_n (length seq1 + maxnext) l))
  end; 
  
val counter = ref 0 ; 
max_compr_number := 200;
fun correct_bl ((i,p),l) = 
  let 
    val _ = incr counter
    val _ = if !counter mod 1000 = 0 then print "." else ()
    val seq1 = valOf (Array.sub (oseq,i))
    val i1 = length seq1
    val l' = penum_wtime 100000 p (length l)
  in
    ((i,p), (length l' < length l, List.tabulate (maxnext, fn x => 
       seq_compare (first_n (i1+x+1) l', first_n (i1+x+1) l) = EQUAL)))
  end;  

PolyML.print_depth 1;
val l0 = filter is_prefix_alt sole; length l0;
val l1 = filter is_continuous l0; length l1;
val l2 = List.mapPartial keep_ext l1; length l2;
val l5 = map correct_bl l2; length l5;
val l6 = list_combine (map (snd o snd) l5);
val l4 = filter (fst o snd) l5;
val l7 = map (fn l => sum_int (map (fn x => if x then 1 else 0) l)) l6;
val l8 = map (fn x => int_div x (length l5)) l7;

fun f (i,x) = (its i ^ " " ^ rts x); 
writel "fast_timeout" ["total", its (length l2), "timeout", its (length l4)];
writel "fast_largeinput" (map f (number_fst 0 (1.0 :: l8)));

writel "small_timeout" ["total", its (length l2), "timeout", its (length l4)];
writel "small_largeinput" (map f (number_fst 0 (1.0 :: l8)));



(* --------------------------------------------------------------------------
   Analysis of the solutions. 
   Many of the solutions were chosen just by looking at the file 
   "result/solutions" produced from isol25.
   -------------------------------------------------------------------------- *)

load "kernel"; open kernel aiLib;
load "human"; open human;

(* reading solutions from the last generation *)
val iprogl = read_iprogl "model/isol25";
val progl = map snd iprogl;

(* reprint solutions in readable form *)
load "bloom"; open bloom;
fun string_of_iprog (i,p) = 
  "A" ^ its i ^ ": " ^ 
  string_of_seq (valOf (Array.sub (oseq,i))) ^ 
  "\n" ^ humanf p;
writel "results/solutions" (map string_of_iprog (dict_sort (snd_compare prog_compare_size) iprogl));

(* frequency of subprograms in solutions *)
val progll = map (mk_fast_set prog_compare o all_subprog) progl;
val prognl = dlist (count_dict (dempty prog_compare) (List.concat progll));
val prognl2 = dict_sort compare_imax prognl;
fun humanif (p,i) = its i ^ ": " ^ humanf p;
writel "results/occurences" (map humanif prognl2);

(* longest program *)
val l1 = map_assoc (prog_size o snd) iprogl;
val l2 = dict_sort compare_imax l1;
val ((an,p),i) = hd l2;
humanf p; an; i;

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

(* largest constant (switch to  3e67eda98b11275a94ea7e7f9ecde3cf25fbb85b) *)
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




