structure qsynt :> qsynt =
struct

open HolKernel Abbrev boolLib aiLib mlTreeNeuralNetwork kernel mcts exec rl;
val ERR = mk_HOL_ERR "qsynt";

val main_tnn = read_tnn (selfdir ^ "/model/tnn17")
val main_iprogl = read_iprogl (selfdir ^ "/model/isol274")

fun test_cache_one target (i,prog) = 
  let val seq = valOf (Array.sub(bloom.oseq,i)) in is_prefix target seq end

fun test_cache target = List.find (test_cache_one target) main_iprogl

fun qsynt target = case search_target main_tnn target of
    NONE =>
  let val l = filter (test_cache_one target) main_iprogl in
    if null l then NONE else
    (
    print_endline "Found in cache"; 
    SOME (hd (dict_sort prog_compare_size (map snd l))) 
    )
  end
  | x => x


end (* struct *)

(* -------------------------------------------------------------------------
   Test oeis-synthesis
   ------------------------------------------------------------------------- 

load "qsynt"; open qsynt;
game.time_opt := SOME 10.0;

val p = valOf (qsynt (map Arbint.fromInt [2,4,16,256]));
print_endline (human.humanf p);
val seq = exec.penum p 10;

val po = qsynt (map Arbint.fromInt [2,5,16,256]);


*)



