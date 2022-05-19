(* This file is used for all kind of post processing/analysis of the solutions *)
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
val iprogl = read_iprogl "model/isol25";
val progl = map snd iprogl;

(* reprint solutions *)
load "bloom"; open bloom;
fun string_of_iprog (i,p) = 
  "A" ^ its i ^ ": " ^ 
  string_of_seq (valOf (Array.sub (oseq,i))) ^ 
  "\n" ^ humanf p;
writel "results/solutions" (map string_of_iprog (dict_sort (snd_compare prog_compare_size) iprogl));

(* frequency *)
val progll = map (mk_fast_set prog_compare o all_subprog) progl;
val prognl = dlist (count_dict (dempty prog_compare) (List.concat progll));
val prognl2 = dict_sort compare_imax prognl;
fun humanif (p,i) = its i ^ ": " ^ humanf p;
writel "results/occurences" (map humanif prognl2);

(* distribution of sizes *)
val sizel = map prog_size (mk_fast_set prog_compare progl);
val sizel2  = dlist (count_dict (dempty Int.compare) sizel);
writel "results/dissize" (map (fn (a,b) => its a ^ " " ^ its b) sizel2);
(* size of programs *)
val n = sum_int (map prog_size progl);
val r = int_div n (length progl);

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

load "execarb"; open execarb;
rt_glob := Timer.startRealTimer (); 
timelimit := 100.0;
val constel = map_assoc (fn (p,i) => mk_execarb p (Arbint.zero,Arbint.zero)) constl; 

val largel = first_n 3 (rev (dict_sort (snd_compare Arbint.compare) constel));
fun humanrif ((p,i),r) = Arbint.toString r ^ ": " ^ its i ^ ": " ^ humanf p;
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

local open Arbint in
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

