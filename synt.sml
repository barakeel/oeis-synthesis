structure synt :> synt =
struct

open HolKernel Abbrev boolLib aiLib kernel mcts execarb mlTreeNeuralNetworkAlt;
val ERR = mk_HOL_ERR "synt";

fun rm_i s = 
  if String.size s = 0 then s else
  if String.sub (s,String.size s - 1) =  #"i" 
  then String.substring (s,0,String.size s - 1)
  else s;

val aits = rm_i o Arbint.toString
fun ailts x = String.concatWith " " (map aits x)
val _ = print_endline "Loading weights"
val main_tnn = read_tnn (selfdir ^ "/main_tnn")
val main_sold = enew prog_compare (read_result (selfdir ^ "/main_sold"))

fun synt tim target =
  let 
    val _ = use_semb := false
    val _ = use_cache := true
    val (po,t) = add_time (search_target_aux (main_tnn,main_sold) tim) target
  in
    case po of 
      NONE => 
      (print_endline ("Could not find a program in " ^ rts t ^ " seconds.");
       NONE)
    | SOME p => (print_endline (rm_par (human p)); SOME p)
  end

fun seq n p = print_endline (ailts (arb_seq_of_prog n p))

end (* struct *)
