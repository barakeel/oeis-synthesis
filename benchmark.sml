(* importing solutions from three loops of the main self-learning run *)
load "rl"; open mlTreeNeuralNetwork kernel rl human aiLib;
fun has_compr (Ins (id,pl)) = id = 12 orelse exists has_compr pl;
fun has_compr2 (i,(a,b)) = has_compr a orelse has_compr b;
val r2 = List.concat (map (fn x => read_iprogl ("model/" ^ x)) 
  ["isol46__altisol","isol47__altisol","isol48__altisol"]);
val r2' = mk_fast_set (cpl_compare Int.compare prog_compare) r2;
val r2'' = filter (not o has_compr o snd) r2';
length r2'';

(* post processing alternative solutions and creating equations *)
val d = dregroup Int.compare r2';
val l1 = filter (fn (i,a) => length a >= 2) (dlist d);  
fun f a = pair_of_list (
  first_n 2 (map fst (dict_sort compare_imin (map_assoc number_of_loops a))));
val l2 = map_snd f l1;

(* sorting equations by size *)
fun ipp_compare ((i1,(a1,b1)), (i2,(a2,b2))) =
  prog_compare_size (Ins (~1,[a1,b1]), Ins (~1, [a2,b2]));
val l3 = dict_sort ipp_compare l2;
val l3'' = filter (not o has_compr2) l3;
length l3'';

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
val l4' = filter (not o has_compr2) l4; length l4';
  
(* printing equations *)
human.polynorm_flag := false;
fun g1 (i,(a,b)) = 
String.concatWith "\n" ["A" ^ its i,
string_of_seq (valOf (Array.sub (bloom.oseq,i))),
 human.humanf a, human.humanf b];
fun g2 (i,(a,b)) = String.concatWith "\n" ["A" ^ its i, 
string_of_seq (valOf (Array.sub (bloom.oseq,i))), 
sexpr a, sexpr b];  
writel "equalities/human_full" (map g1 l4');
writel "equalities/sexpr_full" (map g2 l4');

