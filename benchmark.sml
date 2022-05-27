load "rl"; open mlTreeNeuralNetwork kernel rl human aiLib;
fun has_compr (Ins (id,pl)) = id = 12 orelse exists has_compr pl;

(* -------------------------------------------------------------------------
   Importing solutions from three loops of the main self-learning run 
   ------------------------------------------------------------------------- *)


val data =  map (fn x => "isol" ^ its x ^ "__altisol") 
 [46,47,48,49,50,51,52,53,54];
val r2 = List.concat (map (fn x => read_iprogl ("model/" ^ x)) data);
val r3 = merge_altisol r2;
val r4 = mk_fast_set (cpl_compare Int.compare prog_compare) r3;
val r5 = filter (not o has_compr o snd) r4;
length r5; 

(* -------------------------------------------------------------------------
   Post-processing alternative solutions and creating equations
   ------------------------------------------------------------------------- *)

val d = dregroup Int.compare r5;
val l1 = filter (fn (i,a) => length a >= 2) (dlist d);  
fun f a = pair_of_list (
  first_n 2 (map fst (dict_sort compare_imin (map_assoc number_of_loops a))));
val l2 = map_snd f l1; length l2;
  
(* sorting equations by size *)
fun ipp_compare ((i1,(a1,b1)), (i2,(a2,b2))) =
  cpl_compare prog_compare_size Int.compare
    ((Ins (~1,[a1,b1]),i1), (Ins (~1, [a2,b2]),i2));
val l3 = dict_sort ipp_compare l2; length l3;
val l3' = mk_fast_set ipp_compare l3; length l3';
(* removing duplicates *)
val dsimp = ref (eempty (list_compare prog_compare));
fun rm_dupl (i,(p1,p2)) = 
  let val loopl = all_loops (Ins (~1,[p1,p2])) in
    if emem loopl (!dsimp)
    then NONE
    else (dsimp := eadd loopl (!dsimp); SOME (i,(p1,p2)))
  end;
dsimp := eempty (list_compare prog_compare);
val l4 = List.mapPartial I (map rm_dupl l3);  
length l4;
  
(* -------------------------------------------------------------------------
   Filtering trivial solutions based some compression heuristic.
   ------------------------------------------------------------------------- *)

val ERR = mk_HOL_ERR "test" 

fun test_pair (p1,p2) = 
  let val (n1,n2) = (number_of_loops p1, number_of_loops p2) in
    if n1 < n2 then prog_size p2 < prog_size p1 + (n2 - n1) * 3
    else if n2 < n1 then prog_size p1 < prog_size p2 + (n1 - n2) * 3
    else raise ERR "test_pair" (humanf p1 ^ " ::: " ^ humanf p2)
  end;
  
val l5 = filter (test_pair o snd) l4;
length l5;

(* -------------------------------------------------------------------------
   Printing equations
   ------------------------------------------------------------------------- *)

human.polynorm_flag := false;
fun g1 (i,(a,b)) = 
String.concatWith "\n" ["A" ^ its i, 
string_of_seq (valOf (Array.sub (bloom.oseq,i))),
 human.humanf a, human.humanf b];
fun g2 (i,(a,b)) = String.concatWith "\n" ["A" ^ its i,
string_of_seq (valOf (Array.sub (bloom.oseq,i))), 
sexpr a, sexpr b];  
writel "equalities/human_full" (map g1 l5);
writel "equalities/sexpr_full" (map g2 l5);

