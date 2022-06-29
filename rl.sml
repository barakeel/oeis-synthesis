structure rl :> rl =
struct

open HolKernel Abbrev boolLib aiLib smlParallel smlExecScripts 
  mlTreeNeuralNetwork mcts kernel human bloom exec game check tnn
  

val ERR = mk_HOL_ERR "rl"
type seq = kernel.seq
type prog = kernel.prog
type tnn = mlTreeNeuralNetwork.tnn
type 'a set = 'a Redblackset.set
type ('a,'b) dict = ('a,'b) Redblackmap.dict
type anum = bloom.anum
type eff = int * real option

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)
  
val ncore = ref 
  (string_to_int (dfind "ncore" configd) handle NotFound => 32)
val coreid_glob = ref 0
val ntarget = ref
  (string_to_int (dfind "ntarget" configd) handle NotFound => 32)
val maxgen = ref NONE
val ngen_glob = ref 0
val expname = ref "test"
val tnndir = selfdir ^ "/tnn_in_c"
val loss_threshold = 0.8 (* ignore tnn with a loss above this threshold *)
val cont_flag = ref false (* continous training/searching *)

(* -------------------------------------------------------------------------
   Files
   ------------------------------------------------------------------------- *)

fun expdir () = selfdir ^ "/exp/" ^ !expname
fun log s = (print_endline s; append_endline (expdir () ^ "/log") s)

fun traindir () = expdir () ^ "/train"
fun searchdir () = expdir () ^ "/search"
fun histdir () = expdir () ^ "/hist"
fun tnn_file ngen = histdir () ^ "/tnn" ^ its ngen
fun isol_file ngen = histdir () ^ "/isol" ^ its ngen

fun mk_dirs () = 
  ( 
  mkDir_err (selfdir ^ "/parallel_search");
  mkDir_err (selfdir ^ "/exp");
  mkDir_err (expdir ());
  app mkDir_err [traindir (),searchdir (), histdir ()]
  ) 

fun write_isol_atomic ngen iprogl = 
  let
    val newfile = isol_file ngen
    val oldfile = newfile ^ "_temp"
  in
    write_iprogl oldfile iprogl;
    OS.FileSys.rename {old = oldfile, new = newfile}
  end
  
fun read_isol ngen = read_iprogl (isol_file ngen)

fun is_number s = all Char.isDigit (explode s)

fun find_last s =
  let 
    val sl1 = listDir (histdir ())
    val sl2 = filter (String.isPrefix s) sl1
    val sl3 = mapfilter (snd o split_string s) sl2
    val sl4 = filter is_number sl3
    val il = mapfilter string_to_int sl4
  in
    if null il 
    then raise ERR "find_last" ("no " ^ s)
    else list_imax il
  end

fun find_last_isol () = find_last "isol"
fun find_last_tnn () = find_last "tnn"

fun find_last_notbad s =
  let 
    val sl1 = listDir (histdir ())
    val sl2 = filter (String.isPrefix s) sl1
    val sl3 = mapfilter (snd o split_string s) sl2
    val sl4 = filter is_number sl3
    val il = mapfilter string_to_int sl4
    fun test i = not (exists_file (histdir () ^ "/" ^ s ^ its i ^ "_bad"))
    val il2 = filter test il
  in
    if null il2 
    then raise ERR "find_last_notbad" ("no " ^ s)
    else list_imax il2
  end

fun find_last_ob_notbad () = find_last_notbad "ob"

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun write_tnn_atomic ngen tnn =
  let 
    val newfile = tnn_file ngen
    val oldfile = newfile ^ "_temp"
  in
    write_tnn oldfile tnn;
    OS.FileSys.rename {old = oldfile, new = newfile}
  end

fun trainf () =
  let
    val isol = 
      if !cont_flag 
      then read_isol (find_last_isol ())
      else read_isol (!ngen_glob) 
    val _ = print_endline ("reading isol " ^ (its (length isol)))
    val ex = create_exl (shuffle isol)
    val _ = print_endline (its (length ex) ^ " examples created")
  in
    if !use_mkl then
      let
        val tnnlog_file = tnn_file (!ngen_glob) ^ "_log"
        val tnnsml_file = tnndir ^ "/out_sml"
        val sbin = "./tree"
        val _= 
          (
          print_endline "exporting training data";
          export_traindata ex;
          print_endline "exporting end";
          OS.Process.sleep (Time.fromReal 1.0);
          cmd_in_dir tnndir (sbin ^ " > " ^ tnnlog_file)
          )
        val _ = OS.Process.sleep (Time.fromReal 1.0)
        val tnn = read_ctnn (readl tnnsml_file)
        val obfile = histdir () ^ "/ob" ^ its (!ngen_glob)
        val obfile_temp = obfile ^ "_temp"
        val loss = (valOf o Real.fromString) (last (String.tokens 
          Char.isSpace (last (readl tnnlog_file))))
        val catcmd = "cat ob_fst.c ob_arity ob_head ob_mat ob_snd.c > "  
      in
        cmd_in_dir tnndir (catcmd ^ obfile_temp);
        OS.FileSys.rename {old = obfile_temp, new = obfile};
        write_tnn_atomic (!ngen_glob) tnn;
        if loss < loss_threshold then () else 
          writel_atomic (obfile ^ "_bad") ["Empty file"]
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
      write_tnn_atomic (!ngen_glob) tnn
    end
  end

fun wrap_trainf ngen =
  let
    val scriptfile = !buildheap_dir ^ "/train.sml" 
    val makefile = !buildheap_dir ^ "/Holmakefile"
  in
    writel makefile ["INCLUDES = " ^ selfdir]; 
    writel scriptfile
     [
     "open rl;",
     "rl.expname := " ^ mlquote (!expname) ^ ";",
     "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir) ^ ";",
     "rl.ngen_glob := " ^ its (!ngen_glob) ^ ";",
     "tnn.dim_glob := " ^ its (!dim_glob) ^ ";",
     "tnn.use_mkl := " ^ bts (!use_mkl) ^ ";",
     "tnn.use_ob := " ^ bts (!use_ob) ^ ";",
     "rl.cont_flag := " ^ bts (!cont_flag) ^ ";",
     "trainf ()"
     ];
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
    val _ = if not (exists_file (tnndir ^ "/ob.so")) 
            then use_ob := false else ()
    val _ = if !use_ob then update_fp_op () else ()
    val _ = if can find_last_tnn () then () else 
            (player_glob := player_random; time_opt := SOME 120.0)
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
  in 
    check progl
  end

fun string_of_timeo () = (case !time_opt of
    NONE => "Option.NONE"
  | SOME s => "Option.SOME " ^ rts s)

fun catch_fwrite msg f file x =
  f file x handle Interrupt => raise Interrupt | _ => 
       (print_endline ("rl: " ^ msg ^ ": " ^ file); 
         raise ERR msg file)

fun catch_fread msg f file =
  f file handle Interrupt => raise Interrupt | _ => 
       (print_endline ("rl: " ^ msg ^ ": " ^ file); 
         raise ERR msg file)

val parspec : (tnn, int, (anum * prog) list) extspec =
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
     "tnn.use_ob := " ^ bts (!use_ob),
     "game.time_opt := " ^ string_of_timeo ()] 
    ^ ")"),
  function = search,
  write_param = catch_fwrite "write_tnn" write_tnn,
  read_param = catch_fread "read_tnn" read_tnn,
  write_arg = let fun f file arg = writel file [its arg] 
       in catch_fwrite "write_arg" f end,
  read_arg = let fun f file = string_to_int (hd (readl file)) 
       in catch_fread "read_arg" f end,
  write_result = catch_fwrite "write_iprogl" write_iprogl,
  read_result = catch_fread "read_iprogl" read_iprogl
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
    val tree = starting_tree (mctsobj tnn) []
    val (newtree,t) = add_time (mcts (mctsobj tnn)) tree
  in
    online_flag := false; clean_dicts (); NONE
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

fun human_progfreq (p,freq) = its freq ^ ": " ^ humanf p

fun string_of_iprog (i,p) = 
  "A" ^ its i ^ ": " ^ 
  string_of_seq (valOf (Array.sub (oseq,i))) ^ 
  "\n" ^ humanf p

fun inv_cmp cmp (a,b) = cmp (b,a)

fun string_of_partiprog (i,npl) =
  let 
    val npl' = dict_sort (inv_cmp (fst_compare (fst_compare Int.compare))) npl
    fun f ((n,to),p) = its n ^ (if isSome to then (", " ^ rts (valOf to)) else
      "") ^ ": " ^ humanf p
  in
    "A" ^ its i ^ ": " ^ 
    string_of_seq (valOf (Array.sub (oseq,i))) ^ 
    "\n" ^ String.concatWith " | " (map f npl')
  end

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
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun mk_partial (anum,p) = 
  let fun f x = (length (valOf (Array.sub (oseq, x))), NONE) in
    (anum,[(f anum,p)])
  end
  
fun count_newsol oldisol isoll =
  let 
    val d = ref (enew Int.compare (map fst oldisol))
    val orgn = elength (!d)
    fun loop acc l = case l of
        [] => rev acc
      | _ => let 
               val (l1,l2) = part_n 8 l 
               val l3 = mk_fast_set Int.compare (map fst (List.concat l1))
             in
               d := eaddl l3 (!d);
               loop (elength (!d) - orgn :: acc) l2
             end
    val il = loop [] isoll
  in
    log ("new solutions (after 8 more searches each time): " ^
         String.concatWith " " (map its il)) 
  end



fun rl_search_only ngen =
  let 
    val _ = mk_dirs ()
    val _ = log ("Search " ^ its ngen)
    val _ = buildheap_dir := searchdir () ^ "/" ^ its ngen;
    val _ = mkDir_err (!buildheap_dir)
    val _ = ngen_glob := ngen
    val _ = buildheap_options := 
      "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) 
         handle NotFound => 8000) 
    val (b,tnn) = 
      if !cont_flag 
      then if can find_last_tnn () 
           then (true, read_tnn (tnn_file (find_last_tnn ())))
           else (false, random_tnn (get_tnndim ()))
      else if exists_file (tnn_file (ngen - 1))
           then (true, read_tnn (tnn_file (ngen - 1)))
           else (false, random_tnn (get_tnndim ()))
    val _ = cmd_in_dir tnndir "rm ob.so"
    val _ = if not (!use_ob andalso b) then () else
      let 
        val tnngen = if !cont_flag then find_last_ob_notbad () else ngen - 1
        val obfile = histdir () ^ "/ob" ^ its tnngen
        val obc = tnndir ^ "/ob.c"
        val cpcmd = String.concatWith " " ["cp",obfile,obc]
      in
        cmd_in_dir tnndir cpcmd;
        cmd_in_dir tnndir "sh compile_ob.sh"
      end
    val (isoll,t) = add_time
      (parmap_queue_extern (!ncore) parspec tnn) (List.tabulate (!ntarget,I))
    val _ = log ("search time: " ^ rts_round 6 t)
    val _ = log ("average number of solutions per search: " ^
                  rts_round 2 (average_int (map length isoll)))
    val oldisol = if ngen = 0 then [] else read_isol (ngen - 1)
    val newisol = merge_isol (List.concat (oldisol :: isoll))
    val _ = log ("solutions: " ^ (its (length newisol)))
    val _ = count_newsol oldisol isoll
    val _ = write_isol_atomic ngen newisol
  in
    stats_ngen (!buildheap_dir) ngen
  end

fun rl_train_only ngen =
  let
    val _ = mk_dirs ()
    val _ = log ("Train " ^ its ngen)
    val _ = buildheap_dir := traindir () ^ "/" ^ its ngen
    val _ = mkDir_err (!buildheap_dir)
    val _ = buildheap_options :=
      "--maxheap " ^ its 
      (string_to_int (dfind "train_memory" configd) 
         handle NotFound => 50000) 
    val _ = ngen_glob := ngen
    val (_,t) = add_time wrap_trainf ngen
    val _ = log ("train time: " ^ rts_round 6 t)
  in
    ()
  end



fun rl_search ngen = 
  (
  cont_flag := false;
  rl_search_only ngen; 
  if isSome (!maxgen) andalso ngen >= valOf (!maxgen) then () else 
  rl_train ngen
  )

and rl_train ngen = 
  (
  cont_flag := false; 
  rl_train_only ngen; 
  rl_search (ngen + 1)
  )


fun rl_search_cont () = 
  (
  cont_flag := true;
  ignore (mk_dirs ());
  rl_search_only ((find_last_isol () + 1) handle HOL_ERR _ => 0); 
  rl_search_cont ()
  )

fun wait_isol () = 
  if can find_last_isol () then () else 
     (OS.Process.sleep (Time.fromReal 1.0); wait_isol ())

fun rl_train_cont () = 
  (
  cont_flag := true;
  ignore (mk_dirs ());
  wait_isol ();
  rl_train_only ((find_last_tnn () + 1) handle HOL_ERR _ => 0); 
  rl_train_cont ()
  )

end (* struct *)

(*
(* continuous training *)
load "rl"; open rl;
expname := "603";
rl_train_cont ();

(* continous searching *)
load "rl"; open rl;
expname := "603";
rl_search_cont ();



(* standalone search (run for 2minutes) *)
load "rl"; open mlTreeNeuralNetwork kernel rl human aiLib;
val tnn = random_tnn (tnn.get_tnndim ());
PolyML.print_depth 2;
val isol = search tnn 0;
val isolsort = dict_sort (snd_compare prog_compare_size) isol;
PolyML.print_depth 40;
writel ("aaa_prog") (map string_of_iprog isolsort);

*)
