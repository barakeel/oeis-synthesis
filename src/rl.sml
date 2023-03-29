structure rl :> rl =
struct

open HolKernel Abbrev boolLib aiLib smlParallel smlExecScripts 
  mlTreeNeuralNetwork mcts kernel human bloom exec game check tnn
  

val ERR = mk_HOL_ERR "rl"
type seq = kernel.seq
type prog = kernel.prog
type sol = kernel.sol
type tnn = mlTreeNeuralNetwork.tnn
type 'a set = 'a Redblackset.set
type ('a,'b) dict = ('a,'b) Redblackmap.dict
type anum = bloom.anum
type eff = int * real option

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val nvis = ref
  (string_to_int (dfind "nvis" configd) handle NotFound => 0)
val rtim = ref
  (valOf (Real.fromString (dfind "rtim" configd)) 
   handle NotFound => 600.0)  
   
val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)
val ntarget = (string_to_int (dfind "ntarget" configd) handle NotFound => 32)
val maxgen = ref NONE
val ngen_glob = ref 0
val expname = ref "test"
val tnndir = selfdir ^ "/tnn_in_c"
val modeldir = selfdir ^ "/model"

(* -------------------------------------------------------------------------
   Files
   ------------------------------------------------------------------------- *)

fun expdir () = selfdir ^ "/exp/" ^ !expname
fun log s = (print_endline s; append_endline (expdir () ^ "/log") s)

fun traindir () = expdir () ^ "/train"
fun searchdir () = expdir () ^ "/search"
fun histdir () = expdir () ^ "/hist"
fun itsol_file ngen = histdir () ^ "/itsol" ^ its ngen

fun mk_dirs () = 
  ( 
  mkDir_err (selfdir ^ "/parallel_search");
  mkDir_err (selfdir ^ "/exp");
  mkDir_err (expdir ());
  app mkDir_err [traindir (),searchdir (), histdir ()]
  ) 

fun write_itsol_atomic ngen itprogl = 
  let
    val newfile = itsol_file ngen
    val oldfile = newfile ^ "_temp"
  in
    write_itprogl oldfile itprogl;
    OS.FileSys.rename {old = oldfile, new = newfile}
  end

fun read_itsol ngen = read_itprogl (itsol_file ngen)

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

fun find_last_itsol () = find_last "itsol"
fun find_last_ob () = find_last "ob"

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

val extra_file = selfdir ^ "/model/itsol209"

fun add_extra () =
  if not (!extra_flag) then [] else 
  let val sol = read_itprogl extra_file in 
    List.concat (map (fn (_,x) => map snd x) sol) 
  end

fun trainf_start pid =
  let 
    val execdir = tnndir ^ "/para/" ^ its pid
    val datadir = execdir ^ "/data"
    val _ = app mkDir_err [tnndir ^ "/para", execdir, datadir]
    val _ = cmd_in_dir tnndir ("cp tree " ^ execdir)
    val itsol = read_itsol (find_last_itsol ()) @ 
      (if !extra_flag then read_itprogl extra_file else [])
    val _ = print_endline ("reading itsol " ^ (its (length itsol)))
    val isolaux = map (fn (a,bl) => (a,map snd bl)) itsol
    val isol = distrib isolaux
    val ex = create_exl (shuffle isol)
    val nex = length ex
    val _ = print_endline (its nex ^ " examples created")
    val nep = if nex < 20000 then 100 
              else Real.round (int_div nex 20000) * 100
    val newex = if pid = 0 then ex else first_n 20000 (shuffle ex)
  in
    (
    print_endline "exporting training data";
    export_traindata datadir nep newex;
    print_endline "exporting end"
    )
  end

fun trainf_end pid =
  let
    val execdir = tnndir ^ "/para/" ^ its pid
    val obfile = !buildheap_dir ^ "/ob" ^ 
                 its (!ngen_glob) ^ "_" ^ its pid ^ ".c"
    val obfst = tnndir ^ "/ob_fst.c"
    val obsnd = tnndir ^ "/ob_snd.c"
    val catcmd = String.concatWith " " ["cat",obfst,"out_ob",obsnd,">",obfile]  
  in
    cmd_in_dir execdir catcmd;
    cmd_in_dir tnndir ("sh compile_ob.sh " ^ obfile)
  end

fun trainw_start pid =
  let
    val script1 = !buildheap_dir ^ "/train_start" ^ its pid ^ ".sml" 
    val script2 = !buildheap_dir ^ "/train_end" ^ its pid ^ ".sml" 
    val logfile = !buildheap_dir ^ "/log" ^ its pid
    val preambule = 
      [
       "open rl;",
       "rl.expname := " ^ mlquote (!expname) ^ ";",
       "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir) ^ ";",
       "rl.ngen_glob := " ^ its (!ngen_glob) ^ ";",
       "kernel.dim_glob := " ^ its (!dim_glob) ^ ";"
       ]
  in
    writel script1 (preambule @ ["trainf_start (" ^ its pid ^ ");"]);
    writel script2 (preambule @ ["trainf_end (" ^ its pid ^ ");"])
  end

fun trainw_export pid =
  let val script1 = !buildheap_dir ^ "/train_start" ^ its pid ^ ".sml" in
    exec_script script1
  end
 
fun trainw_middle pid =
  let 
    val execdir = tnndir ^ "/para/" ^ its pid
    val logfile = !buildheap_dir ^ "/log" ^ its pid
  in
    cmd_in_dir execdir ("./tree" ^ " > " ^ logfile)
  end
  
fun trainw_end pid =   
  let val script2 = !buildheap_dir ^ "/train_end" ^ its pid ^ ".sml" in
    exec_script script2
  end

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

fun clean_dicts () = 
  (progd := eempty prog_compare; embd := dempty Term.compare)

fun halfnoise () = 
  if !halfnoise_flag then
    (
    if !ngen_glob mod 2 = 0
    then noise_flag := false
    else (noise_flag := true; noise_coeff_glob := 0.1)
    )
  else noise_flag := false
  

fun load_ob () =
  if !ngen_glob <= 0 then () else  
    let 
      val ns = its (find_last_ob ()) 
      val suffix = its (random_int (0,!train_multi - 1))
      val fileso = traindir () ^ "/" ^ ns ^ "/ob" ^ ns ^ "_" ^ suffix ^ ".so"
    in
      print_endline ("loading " ^ fileso);
      (* update_fp_op fileso *)
      update_fp_op (selfdir ^ "/model/ob_online.so")
    end

(* also used in non-cubing *)
fun init_cube () =
  let
    val _ = print_endline "initialization"
    val _ = search.randsearch_flag := (!ngen_glob <= 0)
    val _ = if !search.randsearch_flag 
            then print_endline "random search"
            else print_endline "tnn-guided search"
    val _ = halfnoise ()
    val _ = load_ob ()
  in
    ()
  end

fun search () targetn =
  let val _ = print_endline "search start" in
    if !beam_flag 
    then search.beamsearch ()
    else (select_random_target (); search.search (!nvis,!rtim); checkfinal ())
  end

fun string_of_timeo () = (case !time_opt of
    NONE => "Option.NONE"
  | SOME s => "Option.SOME " ^ rts s)

val parspec : (unit, int, sol list) extspec =
  {
  self_dir = selfdir,
  self = "rl.parspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "rl.expname := " ^ mlquote (!expname),
     "rl.ngen_glob := " ^ its (!ngen_glob),
     "kernel.dim_glob := " ^ its (!dim_glob),
     "game.time_opt := " ^ string_of_timeo (),
     "rl.init_cube ()"] 
    ^ ")"),
  function = search,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = let fun f file arg = writel file [its arg] in f end,
  read_arg = let fun f file = string_to_int (hd (readl file)) in f end,
  write_result = write_itprogl,
  read_result = read_itprogl
  }

(* -------------------------------------------------------------------------
   Variant of the search function for interactive calls
   ------------------------------------------------------------------------- *)
 
fun mctsobj () = 
  {game = game, mctsparam = mctsparam (), player = !player_glob}; 
   
fun search_target target =
  let
    val _ = clean_dicts ()
    val fileso = modeldir ^ "/ob_online.so"
    val _ = if not (exists_file fileso) 
            then raise ERR "search_target" ""
            else ()
    val _ = update_fp_op fileso
    val _ = player_glob := player_wtnn_cache
    val _ = target_glob := target
    val _ = online_flag := true
    val tree = starting_tree (mctsobj ()) []
    val (newtree,t) = add_time (mcts (mctsobj ())) tree
  in
    online_flag := false; clean_dicts (); NONE
  end
  handle ResultP p => SOME p

(* -------------------------------------------------------------------------
   Variant of the search function for cube and conquer
   ------------------------------------------------------------------------- *)

fun get_boardsc tree = 
  let 
    val maxprob = 1.0 / Real.fromInt ncore
    val leafl = all_leaf tree
    fun f (node,cl,prob) = 
      let fun g (move,r,_) = 
        let val r' = if prob * r > maxprob then maxprob else prob * r in
          ((#apply_move game.game) move (#board node), !rtim * r')
        end 
      in
        map g cl
      end
  in
    List.concat (map f leafl)
  end
    
fun start_cube n =
  let    
    val _ = load_ob ()
    val _ = 
      if !ngen_glob = 0 
      then player_glob := player_random 
      else player_glob := player_wtnn_cache
    val _ = halfnoise ()
    val _ = game.nsim_opt := SOME n
    val _ = game.time_opt := NONE
    val _ = record_flag := false
    val tree = starting_tree (mctsobj ()) []
    val (newtree,t) = add_time (mcts (mctsobj ())) tree
  in
    clean_dicts (); record_flag := false; newtree
  end

fun search_cube () btiml =
  (
  search.randsearch_flag := (!ngen_glob = 0); 
  checkinit ();
  app (fn (board,tim) => search.search_board (0, tim) board) btiml;
  let val l = checkfinal () in
    print_endline ("solutions: " ^ its (length l)); l
  end
  )
  
val cubespec : (unit, (prog list * real) list, sol list) extspec =
  {
  self_dir = selfdir,
  self = "rl.cubespec",
  parallel_dir = selfdir ^ "/cube_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "rl.expname := " ^ mlquote (!expname),
     "rl.ngen_glob := " ^ its (!ngen_glob),
     "kernel.dim_glob := " ^ its (!dim_glob),
     "game.time_opt := " ^ string_of_timeo (),
     "rl.init_cube ()"] 
    ^ ")"),
  function = search_cube,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_proglrl,
  read_arg = read_proglrl,
  write_result = write_itprogl,
  read_result = read_itprogl
  }

val minlim = (!rtim) / (Real.fromInt ncore * 10.0)

fun regroup_cube buf tot l = case l of
    [] => if null buf then [] else [rev buf]
  | (a,sc) :: m => 
    if tot + sc > minlim 
    then (rev buf) :: regroup_cube [(a,sc)] sc m
    else regroup_cube ((a,sc) :: buf) (tot + sc) m

fun sort_cube l1 =
  let val l2 = map_assoc (fn l => sum_real (map snd l)) l1 in
    map fst (dict_sort compare_rmax l2)
  end
  
fun cube () = 
  let
    val tree = start_cube (ncore * 2)
    val l1 = sort_cube (regroup_cube [] 0.0 (shuffle (get_boardsc tree)))
  in
    smlParallel.parmap_queue_extern ncore cubespec () l1
  end

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun compute_freq f sol1 =
  let val freql = dlist 
    (count_dict (dempty prog_compare) (List.concat (map f sol1)))
  in
    dict_sort compare_imax (filter (fn x => snd x >= 10) freql)
  end

fun human_progfreq (p,freq) = its freq ^ ": " ^ humanf p

val abillion = 1000 * 1000 * 1000

fun string_of_tp (t,p) =
  "size " ^ its (prog_size p) ^ ", " ^
  (
  if t < abillion
  then ("correct all, time " ^ its t)
  else ("correct " ^ its (abillion + 10000 - t))
  ) 
  ^ ": " ^ humanf p

fun string_of_itprog (i,tpl) = 
  (if !fs_flag then String.concatWith "o" (rev (Vector.sub (compv,i))) else
  ("A" ^ its i)) ^ ": " ^ string_of_seq (valOf (Array.sub (oseq,i))) ^ "\n" ^
   String.concatWith "\n" (map string_of_tp tpl)

fun stats_sol prefix itsol =
  let
    val itsolsort = dict_sort 
      (snd_compare (list_compare (snd_compare prog_compare_size))) itsol
    val allprog = List.concat (map (map snd o snd) itsol) 
    val freql1 = compute_freq all_subprog allprog
  in
    writel (prefix ^ "prog") (map string_of_itprog itsolsort);
    writel (prefix ^ "freq") (map human_progfreq freql1)
  end

fun stats_ngen dir ngen =
  let 
    val solprev = if ngen = 0 then [] else read_itsol (ngen - 1)
    val solnew = read_itprogl (itsol_file ngen)
    val prevd = dnew Int.compare solprev
    val soldiff = filter (fn (anum,_) => not (dmem anum prevd)) solnew
  in
    stats_sol (dir ^ "/full_") solnew;
    stats_sol (dir ^ "/diff_") soldiff
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun count_newsol olditsol itsoll =
  let 
    val d = ref (enew Int.compare (map fst olditsol))
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
    val il = loop [] itsoll
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
    val (itsoll,t) = 
      if !notarget_flag then add_time cube ()
      else add_time
        (parmap_queue_extern ncore parspec ()) (List.tabulate (ntarget,I))
    val _ = log ("search time: " ^ rts_round 6 t)
    val _ = log ("average number of solutions per search: " ^
                  rts_round 2 (average_int (map length itsoll)))
    val olditsol = if ngen = 0 then [] else read_itsol (ngen - 1)
    val newitsol = merge_itsol (List.concat (olditsol :: itsoll))
    val _ = log ("solutions: " ^ (its (length newitsol)))
    val allprog = List.concat (map (map snd o snd) newitsol)
    val allsize = List.concat (map (map fst o snd) newitsol)
    val _ = log ("programs: " ^ (its (length allprog)))
    val _ = log ("average size: " ^ rts_round 2 
      (average_int (map prog_size allprog)))
    val _ = log ("average time: " ^ rts_round 2 (average_int allsize))
    val _ = count_newsol olditsol itsoll
    val _ = write_itsol_atomic ngen newitsol
  in
    stats_ngen (!buildheap_dir) ngen
  end


fun rl_train_only ngen =
  let
    val _ = mk_dirs ()
    val _ = buildheap_options :=
          "--maxheap " ^ its 
          (string_to_int (dfind "train_memory" configd) 
             handle NotFound => 50000) 
    val _ = ngen_glob := ngen
    val _ = log ("Train " ^ its ngen)
    val _ = buildheap_dir := traindir () ^ "/" ^ its ngen
    val _ = mkDir_err (!buildheap_dir)
    val makefile = !buildheap_dir ^ "/Holmakefile"
    val _ = writel makefile ["INCLUDES = " ^ selfdir]
    fun f () = 
      let val pidl = List.tabulate (!train_multi, I) in
        app trainw_start pidl;
        ignore (parmap_exact (!train_multi) trainw_export pidl);
        ignore (parmap_exact (!train_multi) trainw_middle pidl);
        ignore (parmap_exact (!train_multi) trainw_end pidl)
      end 
    val (_,t) = add_time f ()
    val _ = log ("train time: " ^ rts_round 6 t)
    val obfileout = histdir () ^ "/ob" ^ its (!ngen_glob)
  in
    writel_atomic obfileout []
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop wrappers
   ------------------------------------------------------------------------- *)

fun rl_search ngen = 
  (
  rl_search_only ngen;
  PolyML.fullGC ();
  if isSome (!maxgen) andalso ngen >= valOf (!maxgen) then () else 
  rl_train ngen
  )

and rl_train ngen = 
  (
  rl_train_only ngen;
  PolyML.fullGC ();
  rl_search (ngen + 1)
  )

fun wait_tnn () = 
  if can find_last_ob () then () else 
  (OS.Process.sleep (Time.fromReal 1.0); wait_tnn ())

fun rl_search_cont () = 
  (
  ignore (mk_dirs ());
  let val n = ((find_last_itsol () + 1) handle HOL_ERR _ => 0) in
    if n = 1 then (print_endline "waiting for tnn"; wait_tnn ()) else ();
    rl_search_only n
  end;
  rl_search_cont ();
  PolyML.fullGC ()
  )

fun wait_itsol b = 
  if can find_last_itsol () then () else 
  (
  if b then print_endline "waiting for itsol" else (); 
  OS.Process.sleep (Time.fromReal 1.0); 
  wait_itsol false
  )

val prev_itsol = ref (~1)

fun wait_newitsol b =
  let val n = find_last_itsol () in
    if n <> !prev_itsol then prev_itsol := n else
    (
    if b then print_endline "waiting for new itsol" else (); 
    OS.Process.sleep (Time.fromReal 1.0); 
    wait_newitsol false
    )
  end

fun rl_train_cont () =
  (
  ignore (mk_dirs ());
  wait_itsol true;
  wait_newitsol true;
  rl_train_only ((find_last_ob () + 1) handle HOL_ERR _ => 0); 
  rl_train_cont ();
  PolyML.fullGC ()
  )

end (* struct *)

