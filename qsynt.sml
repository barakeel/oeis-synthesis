structure qsynt :> qsynt =
struct

open HolKernel Abbrev boolLib aiLib mlTreeNeuralNetwork kernel mcts exec rl;
val ERR = mk_HOL_ERR "qsynt";

val main_tnn = read_tnn (selfdir ^ "/model/tnn83")
val main_iprogl = read_iprogl (selfdir ^ "/model/isol88")

fun test_cache_one target (i,prog) = 
  let val seq = valOf (Array.sub(bloom.oseq,i)) in is_prefix target seq end

fun test_cache target = List.find (test_cache_one target) main_iprogl

fun qsynt target = 
  let val l = filter (test_cache_one target) main_iprogl in
    if null l then search_target main_tnn target else
    (
    print_endline "Found in cache"; 
    SOME (hd (dict_sort prog_compare_size (map snd l))) 
    )
  end

end (* struct *)

(* -------------------------------------------------------------------------
   Test oeis-synthesis
   ------------------------------------------------------------------------- 

load "qsynt"; open aiLib human exec rl qsynt;
tnn.use_ob := false;
game.time_opt := SOME 60.0;
val po = qsynt (map Arbint.fromInt [2,4,16,256]);
val p = valOf po;
print_endline (humanf p);
val seq = penum p 10;

*)



