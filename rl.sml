structure rl :> rl =
struct

open HolKernel Abbrev boolLib aiLib smlParallel smlExecScripts 
  mlTreeNeuralNetwork
  mcts kernel human bloom exec game check tnn
  

val ERR = mk_HOL_ERR "rl"
type seq = kernel.seq
type prog = kernel.prog
type tnn = mlTreeNeuralNetwork.tnn
type 'a set = 'a Redblackset.set
type ('a,'b) dict = ('a,'b) Redblackmap.dict
type anum = bloom.anum

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val ncore = ref 15
val coreid_glob = ref 0
val ntarget = ref 150
val maxgen = ref NONE
val ngen_glob = ref 0
val expname = ref "test"

(* -------------------------------------------------------------------------
   Logging function
   ------------------------------------------------------------------------- *)

fun log s = 
  (
  print_endline s;
  append_endline (selfdir ^ "/exp/" ^ !expname ^ "/log") s
  )

(* -------------------------------------------------------------------------
   Merging solutions from different processes
   ------------------------------------------------------------------------- *)

fun merge_altisol isol = 
  let 
    val d = ref (dempty (cpl_compare Int.compare Int.compare))
    fun forget ((a,b),c) = (a,c)  
  in
    app (update_altwind_one d) isol;
    map forget (dlist (!d))
  end
  
fun merge_isol isol = 
  let val d = ref (dempty Int.compare) in
    app (update_wind_one d) isol;
    dlist (!d)
  end

(* -------------------------------------------------------------------------
   Files
   ------------------------------------------------------------------------- *)

fun tnn_file ngen = selfdir ^ "/exp/" ^ !expname ^ "/tnn" ^ its ngen
fun isol_file ngen = selfdir ^ "/exp/" ^ !expname ^ "/isol" ^ its ngen
fun ocache_file ngen = selfdir ^ "/exp/" ^ !expname ^ "/ocache" ^ its ngen

fun get_expdir () = selfdir ^ "/exp/" ^ !expname

fun mk_dirs () = 
  let val expdir = selfdir ^ "/exp/" ^ !expname in
    mkDir_err (selfdir ^ "/exp");
    mkDir_err expdir;
    mkDir_err (selfdir ^ "/parallel_search");
    expdir
  end

fun write_isol ngen tmpname iprogl = 
  (
  write_iprogl (isol_file ngen ^ tmpname) iprogl;
  write_iprogl (isol_file ngen) iprogl
  )
fun read_isol ngen = read_iprogl (isol_file ngen)

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun trainf tmpname =
  let 
    val isol = read_isol (!ngen_glob) 
    val _ = print_endline ("reading isol " ^ (its (length isol)))
    val ex = create_exl (shuffle isol)
    val _ = print_endline (its (length ex) ^ " examples created")
  in
    if !use_mkl then
      let
        val tnnlog_file = tnn_file (!ngen_glob) ^ tmpname ^ "_C"
        val tnnsml_file = selfdir ^ "/tnn_in_c/out_sml"
        val sbin = "./tree"
        val _= 
          (
          print_endline "exporting training data";
          export_traindata ex;
          print_endline "exporting end";
          OS.Process.sleep (Time.fromReal 1.0);
          cmd_in_dir (selfdir ^ "/tnn_in_c") 
          (sbin ^ " > " ^ tnnlog_file)
          )
        val _ = OS.Process.sleep (Time.fromReal 1.0)
        val tnn = read_ctnn (readl tnnsml_file)
      in
        write_tnn (tnn_file (!ngen_glob) ^ tmpname) tnn;
        write_tnn (tnn_file (!ngen_glob)) tnn
      end
    else
    let
      val schedule =
        [
         {ncore = 4, verbose = true, learning_rate = 0.001,
          batch_size = 1, nepoch = 50},
         {ncore = 4, verbose = true, learning_rate = 0.0005,
          batch_size = 1, nepoch = 50},
         {ncore = 4, verbose = true, learning_rate = 0.0002,
          batch_size = 1, nepoch = 50},
         {ncore = 4, verbose = true, learning_rate = 0.0001,
          batch_size = 1, nepoch = 50}
        ]
      val tnndim = get_tnndim ()
      val (tnn,t) = add_time (train_tnn schedule (random_tnn tnndim)) 
        (part_pct 1.0 (shuffle ex))
    in
      write_tnn (tnn_file (!ngen_glob) ^ tmpname) tnn;
      write_tnn (tnn_file (!ngen_glob)) tnn
    end
  end

fun wrap_trainf ngen tmpname =
  let
    val scriptfile = !buildheap_dir ^ "/train.sml" 
    val makefile = !buildheap_dir ^ "/Holmakefile"
  in
    writel makefile ["INCLUDES = " ^ selfdir]; 
    writel scriptfile
    ["open rl;",
     "rl.expname := " ^ mlquote (!expname) ^ ";",
     "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir) ^ ";",
     "rl.ngen_glob := " ^ its (!ngen_glob) ^ ";",
     "tnn.dim_glob := " ^ its (!dim_glob) ^ ";",
     "tnn.use_mkl := " ^ bts (!use_mkl) ^ ";",
     "trainf " ^ mlquote tmpname];
     exec_script scriptfile
  end

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

fun clean_dicts () = 
  (progd := eempty prog_compare; 
   embd := dempty Term.compare)

fun init_search coreid =
  let
    val _ = print_endline "initialization"
    val _ = coreid_glob := coreid
    val _ = player_glob := player_wtnn_cache
    val isol = if !ngen_glob <= 0 then [] else read_isol (!ngen_glob - 1)
    val _ = noise_flag := false
    val _ = if !coreid_glob mod 2 = 0 
            then (noise_flag := true; noise_coeff_glob := 0.1) else ()
    fun loop () = 
      let val i = random_int (0,Array.length oseq - 1) in
        case Array.sub (oseq, i) of NONE => loop () | SOME seq => (seq,i)
      end
    val (targetseq,seqname) = loop ()
    val _ = target_glob := targetseq
    val _ = print_endline 
      ("target " ^ its seqname ^ ": " ^ string_of_seq (!target_glob));
  in
    record_flag := true;
    clean_dicts ()
  end

fun end_search () = 
  let val r = elist (!progd) in
    record_flag := false;
    clean_dicts ();
    r
  end

fun mctsobj tnn = 
  {game = game, mctsparam = mctsparam (), player = !player_glob tnn};

fun init_check () =
  if exists_file (ocache_file (!ngen_glob)) 
  then ocache := read_ocache (ocache_file (!ngen_glob))
  else ocache := dempty prog_compare

fun end_check () = ocache := dempty prog_compare

fun search tnn coreid =
  let
    val _ = init_search coreid
    val _ = print_endline "search start"
    val _ = 
      let 
         val tree = starting_tree (mctsobj tnn) []
         val (newtree,t) = add_time (mcts (mctsobj tnn)) tree 
      in
        print_endline ("tree_size: " ^ its (tree_size newtree));
        print_endline ("search time: "  ^ rts_round 2 t ^ " seconds")
      end
    val progl = end_search ()
    val _ = init_check ();
    val r = check progl
    val _ = end_check ()
  in 
    r
  end

fun string_of_timeo () = (case !time_opt of
    NONE => "Option.NONE"
  | SOME s => "Option.SOME " ^ rts s)

val parspec : (tnn, int, (int * prog) list * (int * prog) list) extspec =
  {
  self_dir = selfdir,
  self = "rl.parspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "rl.expname := " ^ mlquote (!expname),
     "rl.ngen_glob := " ^ its (!ngen_glob),
     "rl.coreid_glob := " ^ its (!coreid_glob),
     "tnn.dim_glob := " ^ its (!dim_glob),
     "game.time_opt := " ^ string_of_timeo ()] 
    ^ ")"),
  function = search,
  write_param = write_tnn,
  read_param = read_tnn,
  write_arg = let fun f file arg = writel file [its arg] in f end,
  read_arg = let fun f file = string_to_int (hd (readl file)) in f end,
  write_result = let fun f file (r1,r2) = (write_iprogl (file ^ "_r1") r1;
                                           write_iprogl (file ^ "_r2") r2) 
                 in f end,
  read_result = let fun f file = 
    (read_iprogl (file ^ "_r1"), read_iprogl (file ^ "_r2")) in f end
  }

(* -------------------------------------------------------------------------
   Variant of the search function for interactive calls
   ------------------------------------------------------------------------- *)


fun search_target tnn target =
  let
    val _ = player_glob := player_wtnn_cache
    val _ = noise_flag := true
    val _ = target_glob := target
    val _ = online_flag := true
    val _ = timeincr := long_timeincr 
    val tree = starting_tree (mctsobj tnn) []
    val (newtree,t) = add_time (mcts (mctsobj tnn)) tree
  in
    online_flag := false; timeincr := short_timeincr; clean_dicts (); NONE
  end
  handle ResultP p => SOME p

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun compute_freq f sol1 =
  let val freql = dlist 
    (count_dict (dempty prog_compare) (List.concat (map f sol1)))
  in
    dict_sort compare_imax freql
  end

fun string_of_iprog (i,p) = 
  "A" ^ its i ^ ": " ^ 
  string_of_seq (valOf (Array.sub (oseq,i))) ^ 
  "\n" ^ humanf p;

fun human_progfreq (p,freq) = its freq ^ ": " ^ humanf p;

fun stats_sol prefix isol =
  let
    val isolsort = dict_sort (snd_compare prog_compare_size) isol
    val freql1 = compute_freq all_subprog (map snd isol)
  in
    writel (prefix ^ "prog") (map string_of_iprog isolsort);
    writel (prefix ^ "freq") (map human_progfreq freql1)
  end

fun stats_ngen dir ngen =
  let 
    val solprev = 
      if ngen = 0 then [] else read_iprogl (isol_file (ngen - 1))
    val solnew = read_iprogl (isol_file ngen)
    val prevd = dnew Int.compare solprev
    val soldiff = filter (fn (i,_) => not (dmem i prevd)) solnew
  in
    stats_sol (dir ^ "/full_") solnew;
    stats_sol (dir ^ "/diff_") soldiff
  end

(* -------------------------------------------------------------------------
   Caching slow OEIS sequences
   ------------------------------------------------------------------------- *)

fun update_ocache ngen pl =
  let 
    val prevcache = 
      if exists_file (ocache_file (ngen - 1))
      then read_ocache (ocache_file (ngen - 1))
      else dempty prog_compare 
    fun f p = case dfindo p prevcache of
      SOME v => ocache := dadd p v (!ocache) 
    | NONE => add_ocache p
  in
    ocache := dempty prog_compare;
    app f pl;
    write_ocache (ocache_file ngen) (!ocache)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_search_only tmpname ngen =
  let 
    val expdir = mk_dirs ()
    val _ = log ("Search " ^ its ngen)
    val _ = buildheap_dir := expdir ^ "/search" ^ its ngen ^ tmpname;
    val _ = mkDir_err (!buildheap_dir)
    val _ = ngen_glob := ngen
    val _ = buildheap_options := "--maxheap 12000"
    val tnn = if ngen <= 0 
              then random_tnn (get_tnndim ())
              else read_tnn (tnn_file (ngen - 1))
    val isol = if ngen - 1 <= ~1
               then []
               else read_isol (ngen - 1)
    val (_,t) = add_time (update_ocache ngen) (map snd isol)
    val _ = log ("ocache time: " ^ rts_round 6 t)
    val (iprogll_both,t) = add_time
      (parmap_queue_extern (!ncore) parspec tnn) (List.tabulate (!ntarget,I))
    val (iprogll, iprogll_alt) = split iprogll_both
    val _ = log ("search time: " ^ rts_round 6 t)
    val _ = log ("solutions for each search:")
    val _ = log (String.concatWith " " (map (its o length) iprogll))
    val newisol = merge_isol (List.concat (isol :: iprogll))
    val newaltisol = merge_altisol (List.concat (isol :: iprogll_alt))
  in
    write_isol ngen tmpname newisol;
    write_iprogl (isol_file ngen ^ "__altisol") newaltisol;
    log ("solutions: " ^ (its (length newisol)));
    stats_ngen (!buildheap_dir) ngen
  end

and rl_search tmpname ngen = 
  (rl_search_only tmpname ngen; 
   if isSome (!maxgen) andalso ngen >= valOf (!maxgen) then () else 
   rl_train tmpname ngen)

and rl_train_only tmpname ngen =
  let
    val expdir = mk_dirs ()
    val _ = log ("Train " ^ its ngen)
    val _ = buildheap_dir := expdir ^ "/train" ^ its ngen ^ tmpname
    val _ = mkDir_err (!buildheap_dir)
    val _ = buildheap_options := "--maxheap 100000"
    val _ = ngen_glob := ngen
    val (_,t) = add_time (wrap_trainf ngen) tmpname 
    val _ = log ("train time: " ^ rts_round 6 t)
  in
    ()
  end

and rl_train tmpname ngen = 
  (rl_train_only tmpname ngen; rl_search tmpname (ngen + 1))

end (* struct *)

(*
(* Train on the oeis *)
load "rl"; open rl;
expname := "run312";
rl_search "_main10" 75;

(* standalone search *)
load "rl"; open mlTreeNeuralNetwork kernel rl human aiLib;
time_opt := SOME 60.0;
val tnn = random_tnn (get_tnndim ());
PolyML.print_depth 2;
val (r1,_) = search tnn 1;
PolyML.print_depth 40;
length r1;

app print_endline (map string_of_iprog l);


*)