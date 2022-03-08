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

val aol2 = map_snd (string_to_int o tl_string) (bloom.import_arbseq_fst ())

fun nmatch_seq (seq1,seq2) = case (seq1,seq2) of
    ([],_) => (0,true)
  | (_,[]) => (0,true)
  | (a1 :: m1, a2 :: m2) => 
    if a1 <> a2 then (0,false) else 
    let val (n,b) = nmatch_seq (m1,m2) in
      (n+1,b)
    end

fun find_largest a l = case l of
    [] => a
  | b :: m => if snd b > snd a then find_largest b m else find_largest a m


fun after_n n l = snd (part_n n l)

fun score_match gseq (seq,anum) = 
  let 
    val anumr = Real.fromInt anum / 10000000.0
    fun scoref (matchn,contb,shiftn) =
      Real.fromInt matchn * Math.pow (0.95, Real.fromInt shiftn) 
      * (if contb then 1.0 else 0.5) - anumr
    fun loop shiftn n cseq = 
      if null cseq orelse shiftn >= n then [] else
      let val (matchn,contb) = nmatch_seq (gseq,cseq) in
        ((matchn,contb,shiftn,anum), scoref (matchn,contb,shiftn))
        :: loop (shiftn + 1) n (tl cseq)
      end
    val l = loop 0 16 seq
  in    
    if null l then NONE else 
    SOME (find_largest (hd l) (tl l))
  end

fun string_match (matchn,contb,shiftn,anum) =
  let val anums =  "A" ^ its anum in
    "<a href=https://oeis.org/search?q=" ^ anums ^ ">" ^ anums ^ "</a>" ^
    "(" ^ its shiftn ^ "-" ^ its (shiftn + matchn) ^ ")"
  end

fun print_matchl n gseq =
  let 
    val l = List.mapPartial (score_match gseq) aol2 
    fun test (x,_) = #1 x >= n
    val l2 = filter test l
    val l3 = map fst (first_n 3 (dict_sort compare_rmax l2))
  in
    if null l3
    then 
      print_endline (
        "Proposed sequence does not match any " ^
        "<a href=https://oeis.org>OEIS</a> sequences. ")
    else 
      print_endline ("Generated sequence matches best with: " ^ 
        String.concatWith ", " (map string_match l3)) 
  end

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
        (print_endline ("Could not find a program in " ^ rts_round 2 t ^ 
         " seconds.");
         NONE)
    | SOME p => 
      let val gseq = arb_seq_of_prog 100 p in
        print_endline ("First " ^ its (Int.min (length gseq,n)) ^ 
          " generated numbers " ^
          "(f(0),f(1),f(2),...):");
        print_endline (ailts (first_n n gseq));
        print_matchl (length target) gseq;
        print_endline "";
        print_endline ("Program found in " ^ rts_round 2 t ^ 
          " seconds (see " ^ 
          "<a href=https://arxiv.org/abs/2202.11908>preprint</a>): ");
        print_endline ("f(x) := " ^ rm_par (humanf p));
        print_endline "";
        print_endline "Python program:\n";
        print_endline (humani (Int.min (length gseq,n)) p);
        print_endline "";
        print "<code>";
        print_endline (humani (Int.min (length gseq,n)) p);
        print_endline "</code>";
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
val _ = synt 600.0 16 [1,10,100,1000];
val _ = synt 600.0 16 [2,3,5,7,11,13,17,19,23,29];
*)
