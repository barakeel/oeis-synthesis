structure web :> web =
struct

open HolKernel Abbrev boolLib aiLib mlTreeNeuralNetwork
  mcts kernel human bloom exec rl;
val ERR = mk_HOL_ERR "web";

val main_tnn = read_tnn (selfdir ^ "/model/tnn24")
val main_iprogl = read_iprogl (selfdir ^ "/model/isol25")

(* -------------------------------------------------------------------------
   Test if the input sequence is in the cache
   ------------------------------------------------------------------------- *)

fun is_prefix seq1 seq2 = case (seq1,seq2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => if a1 = a2 then is_prefix m1 m2 else false

fun test_cache_one target (i,prog) = 
  let val seq = valOf (Array.sub(bloom.oseq,i)) in is_prefix target seq end

fun test_cache target = List.find (test_cache_one target) main_iprogl

(* -------------------------------------------------------------------------
   Generated sequence
   ------------------------------------------------------------------------- *)

fun gseq_result gseq =
  (
  print_endline ("First " ^ its (length gseq) ^ 
    " generated terms (f(0),f(1),f(2),...):");
  print_endline (string_of_seq gseq)
  )

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

fun score_oeis gseq (anum,seq) = 
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
    val l = loop 0 3 seq
  in    
    if null l then NONE else SOME (find_largest (hd l) (tl l))
  end

fun print_oeis (matchn,contb,shiftn,anum) =
  let val anums =  "A" ^ its anum in
    "<a href=https://oeis.org/search?q=" ^ anums ^ ">" ^ anums ^ "</a>" ^
    "(" ^ its shiftn ^ "-" ^ its (shiftn + matchn) ^ ")"
  end

fun oeis_result n gseq =
  let 
    val l1 = List.mapPartial (score_oeis gseq) oseql
    val l2 = map fst (first_n 3 (dict_sort compare_rmax l1))
  in      
    print_endline ("Generated sequence matches best with: " ^ 
    String.concatWith ", " (map print_oeis l2)) 
  end

(* -------------------------------------------------------------------------
   Generated program
   ------------------------------------------------------------------------- *)

fun prog_result p =
  (
  print_endline ("Program found:");
  print_endline ("f(x) := " ^ rm_par (humanf p))
  )

fun python_result gseq p =
  (
  print_endline "Equivalent Python program:";
  print "<code>";
  print_endline (human_python (length gseq) p);
  print_endline "</code>"
  )

(* -------------------------------------------------------------------------
   Main function
   ------------------------------------------------------------------------- *)

fun parse_seq s = map Arbint.fromString 
  (String.tokens (fn x => mem x [#",",#"\n",#" ",#"\t",#"\r"]) s)

fun web_result n po = case po of
    NONE => print_endline "Could not find a covering program" 
  | SOME p => 
    let val gseq = penum p n handle NotFound => [] in
      gseq_result gseq;
      oeis_result n gseq;
      prog_result p;
      python_result gseq p
    end

fun web n targets = 
  let 
    val target = parse_seq targets
    val l = filter (test_cache_one target) main_iprogl
    val po =
      if null l then (print_endline "Starting search";  
        search_target main_tnn target) else
      (
      print_endline "Found in cache"; 
      SOME (hd (dict_sort prog_compare_size (map snd l))) 
      )
  in
    web_result n po
  end

fun add_gap n = print_endline (String.concat (List.tabulate (n,fn _ => "\n")))



end (* struct *)

(* -------------------------------------------------------------------------
   Test oeis-synthesis
   ------------------------------------------------------------------------- 

load "web"; open aiLib human exec rl web;
time_opt := SOME 60.0;

val po = web 32 "2 4 16 256";
val po = web 32 "2 3 5 7";

val p = valOf po;
print_endline (humanf p);
val seq = penum p 10;
*)
