structure synt :> synt =
struct

open HolKernel Abbrev boolLib aiLib kernel mcts mlTreeNeuralNetworkAlt;
val ERR = mk_HOL_ERR "synt";

val _ = print_endline "Loading weights..."
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
      print_endline ("Could not find a program in " ^ rts t ^ " seconds.")
    | SOME p => 
      print_endline (rm_par (human p))
  end

end (* struct *)











