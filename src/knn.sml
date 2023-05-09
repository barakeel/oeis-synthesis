structure knn :> knn =
struct

open HolKernel Abbrev boolLib aiLib kernel mlFeature
val ERR = mk_HOL_ERR "knn"

(* features *)
fun string_of_id id = Char.toString (Char.chr (65 + id))
fun string_of_prog (Ins (id,pl)) = 
  String.concat (map string_of_prog pl @ [string_of_id id]);
fun hash_prog p = hash_string (string_of_prog p); 
fun fea_of_prog p = 
  let 
    val l1 = mk_fast_set prog_compare (all_subprog p)
    val l2 = map hash_prog l1
  in
    dict_sort Int.compare l2
  end

(* knn *)
fun knn_dist symweight feao feap =
  let
    val feai = inter_increasing feao feap
    fun wf n = dfind n symweight handle NotFound => raise ERR "knn_dist" ""
    val weightl = map wf feai
  in
    sum_real weightl / (Real.fromInt (length feao) +
                        Real.fromInt (length feap) - Real.fromInt (length feai))
  end

fun knn_sortu cmp n (symweight,feav) feao =
  let
    fun g x = SOME (x, dfind x symweight) handle NotFound => NONE
    val feaosymweight = dnew Int.compare (List.mapPartial g feao)
    fun f (x,feap) = (x, knn_dist feaosymweight feao feap)
  in
    best_n_rmaxu cmp n (map f feav)
  end

fun knn (symweight,feav) n p = 
  knn_sortu prog_compare_size n (symweight,feav) (fea_of_prog p) 

fun knn_gpt_one dir (symweight,feav) n i s =
  let 
    val p = prog_of_gpt s
    val pl = knn_sortu prog_compare (n+1) (symweight,feav) (fea_of_prog p) 
  in
    if i mod 100 = 0 then append_endline (dir ^ "/log") (its i) else ();
    if hd pl = p then () else 
      raise ERR "knn_gpt_one" ("not closest to itself: " ^ gpt_of_prog p)
    String.concatWith " : " (s :: map gpt_of_prog (tl pl))
  end
  
fun knn_gpt expname n =
  let 
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = erase_file (dir ^ "/log")
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = mkDir_err dir
    val sl = readl (dir ^ "/input")
    val sl' = mk_fast_set String.compare sl
    val progl = map prog_of_gpt sl'
    val feav = map_assoc fea_of_prog progl
    val symweight = learn_tfidf feav
    val (r,t) = add_time (mapi (knn_gpt_one dir (symweight,feav) n)) sl'
  in
    append_endline (dir ^ "/log") ("time: " ^ rts t);
    writel (dir ^ "/output") r
  end  
   
end

(*
load "knn"; load "human"; open mlFeature aiLib kernel knn human;

val sol = read_itprogl "model/itsol209";
val progl = mk_fast_set prog_compare_size (map snd (List.concat (map snd sol)));
val feav = map_assoc fea_of_prog progl; 
val symweight = learn_tfidf feav;
val p = random_elem progl;
val l = knn (symweight,feav) 10 p;


val gptl = map gpt_of_prog progl;
writel "aatest" gptl;

load "knn"; 
knn.knn_gpt "knn" 1;




*)
