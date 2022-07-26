structure qsynt :> qsynt =
struct

open HolKernel Abbrev boolLib aiLib mlTreeNeuralNetwork kernel mcts exec rl;
val ERR = mk_HOL_ERR "qsynt";

val main_tnn = read_tnn (selfdir ^ "/model/tnn_online")
val main_iprogl = read_iprogl (selfdir ^ "/model/isol_online")

fun test_cache_one target (i,prog) = 
  let val seq = valOf (Array.sub(bloom.oseq,i)) in is_prefix target seq end

fun test_cache target = List.find (test_cache_one target) main_iprogl

fun afs s = 
  if String.size s > 285 then NONE else SOME (Arbint.fromString s)  

fun parse_seq s = List.mapPartial afs 
  (String.tokens (fn x => mem x [#",",#"\n",#" ",#"\t",#"\r"]) s)

fun qsynt targets = 
  let val target = parse_seq targets in
  case search_target main_tnn target of
    NONE =>
    let val l = filter (test_cache_one target) main_iprogl in
      if null l then NONE else
      (
      print_endline "Found in cache"; 
      SOME (hd (dict_sort prog_compare_size (map snd l))) 
      )
    end
  | x => x
  end


end (* struct *)

(* -------------------------------------------------------------------------
   Test oeis-synthesis
   ------------------------------------------------------------------------- 

load "qsynt"; open qsynt;

(* make search times out after 10 seconds *)
game.time_opt := SOME 10.0;
(* launch the search *)
val p = valOf (qsynt "2 4 16 256");
(* result in native programming language *)
aiLib.print_endline (human.humanf p);
(* result in Python *)
aiLib.print_endline (human.human_python 10 p);
(* first n generated terms *)
val seq = exec.penum p 10;

(* an example where the search fails *)
val po = qsynt "2 5 16 256";


*)



