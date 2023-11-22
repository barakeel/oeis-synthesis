structure knn :> knn =
struct

open HolKernel Abbrev boolLib aiLib kernel mlFeature smlParallel
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
    if i mod 100 = 0 then print_endline (its i) else ();
    if hd pl = p then () else 
      raise ERR "knn_gpt_one" ("not closest to itself: " ^ gpt_of_prog p);
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

(* -------------------------------------------------------------------------
   Parallel execution
   ------------------------------------------------------------------------- *)

fun knnspec_fun (n,expname) localsl =
  let  
    val dir = selfdir ^ "/exp/" ^ expname
    val sl = readl (dir ^ "/input")
    val sl' = mk_fast_set String.compare sl
    val progl = map prog_of_gpt sl'
    val feav = map_assoc fea_of_prog progl
    val symweight = learn_tfidf feav
    val (newsl,t) = add_time 
      (mapi (knn_gpt_one dir (symweight,feav) n)) localsl
  in
    print_endline ("time: " ^ rts t);
    newsl
  end

val knnspec : (int * string, string list, string list) extspec =
  {
  self_dir = selfdir,
  self = "knn.knnspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = knnspec_fun,
  write_param = let fun f file (i,s) = writel file [its i, s] in f end,
  read_param = let fun f file = 
      let val sl = readl file in (string_to_int (hd sl), hd (tl sl)) end 
    in f end,
  write_arg = writel,
  read_arg = readl,
  write_result = writel,
  read_result = readl
  }

fun parallel_knn_gpt ncore expname n =
  let  
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = erase_file (dir ^ "/log")
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val sl = readl (dir ^ "/input")
    val sl' = mk_fast_set String.compare sl
    val sll = cut_n (3*ncore) sl'
    val (newsll,t) = 
      add_time (parmap_queue_extern ncore knnspec (n,expname)) sll
  in
    writel (dir ^ "/log") ["time: " ^ rts t];
    writel (dir ^ "/output") (List.concat newsll)
  end

(* -------------------------------------------------------------------------
   Clustering algorithm
   ------------------------------------------------------------------------- *)

fun cluster_aux ncluster proglset =
  let 
    val csize = (length proglset div ncluster) + 1
    val feav = map_assoc fea_of_prog proglset
    val symweight = mlFeature.learn_tfidf feav 
    fun loop n feavloc =
      if null feavloc then [] else 
      if n <= 1 then [map fst feavloc] else
      let
        val _ = print_endline (its n)       
        val sel = knn (symweight,feavloc) csize (fst (random_elem feavloc))
        val d = enew prog_compare sel
        val newfeav = filter (fn x => not (emem (fst x) d)) feavloc
      in
        sel :: loop (n-1) newfeav
      end
  in   
    loop ncluster feav
  end  

fun random_cluster nex progl =
  let val ncluster = (length progl div nex) + 1 in
    random_elem (cluster_aux ncluster progl)
  end

fun cluster expname ncluster =
  let 
    val dir = selfdir ^ "/exp/" ^ expname
    val sl = readl (dir ^ "/input")
    val sl' = mk_fast_set String.compare sl
    val progl = map prog_of_gpt sl'
    val proglset = mk_fast_set prog_compare_size progl
    fun f i x = writel (dir ^ "/cluster" ^ its i) (map gpt_of_prog x)
  in   
    appi f (cluster_aux ncluster proglset)
  end
  
(* -------------------------------------------------------------------------
   Clustering algorithm 2
   ------------------------------------------------------------------------- *)

fun random_cluster2 (feav,symweight) csize pl =
  knn (symweight,feav) csize (random_elem pl)

fun cluster2 expname ncluster csize =
  let
    val dir = selfdir ^ "/exp/" ^ expname
    val sl = readl (dir ^ "/input")
    val sl' = mk_fast_set String.compare sl
    val progl = map prog_of_gpt sl'
    val proglset = mk_fast_set prog_compare_size progl
    (* val csize = (length proglset div ncluster) + 1 *)
    val feav = map_assoc fea_of_prog proglset
    val symweight = mlFeature.learn_tfidf feav
    fun loop n feavloc =
      if null feavloc then [] else
      if n <= 0 then [] else
      (* if n <= 1 then [map fst feavloc] else *)
      let
        val _ = print_endline (its n)      
        val sel = random_cluster2 (feavloc,symweight) csize (map fst feavloc)
        val d = enew prog_compare sel
        val newfeav = filter (fn x => not (emem (fst x) d)) feavloc
      in
        sel :: loop (n-1) newfeav
      end
    fun f i x = writel (dir ^ "/cluster" ^ its i) (map gpt_of_prog x)
  in  
    appi f (loop ncluster feav)
  end




end

(*
load "knn"; 
knn.knn_gpt "knn" 1;
knn.parallel_knn_gpt 2 "knn1" 1;
knn.cluster "knn1" 5; 
*)




