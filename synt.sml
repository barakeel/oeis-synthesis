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

fun parse_seq s = first_n 50 (
  map string_to_int 
    (String.tokens (fn x => mem x [#",",#"\n",#" ",#"\t",#"\r"]) s))

fun synt tim n target =
  let
    val _ = use_semb := false
    val _ = use_cache := true
    val _ = noise_flag := true
    val _ = uniform_flag := true
    val (po,t) = add_time (search_target_aux (main_tnn,main_sold) tim) target
  in
    case po of 
      NONE => 
        (print_endline ("Could not find a program in " ^ rts t ^ " seconds.");
         NONE)
    | SOME p => 
      let val r = arb_seq_of_prog n p in
        print_endline ("First " ^ its (length r) ^ " generated numbers " ^
          "(f(0),f(1),f(2),...):");
        print_endline (ailts r ^ "\n");
        print_endline "Program with definitions from the paper:";
        print_endline ("f(x) := " ^ rm_par (humanf p) ^ "\n");
        print "<code>";
        print_endline (humani n p);
        print "</code>";
        SOME p
      end
  end

fun add_gap n = print_endline (String.concat (List.tabulate (n,fn _ => "\n")));

end (* struct *)

(* -------------------------------------------------------------------------
   Test oeis-synthesis
   ------------------------------------------------------------------------- 

load "synt"; open synt;
val _ = synt 600.0 16 [1,12,123,1234];
val _ = synt 600.0 16 [2,3,5,7,11,13,17,19,23,29];
*)
