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
   Statistics (prime)
   ------------------------------------------------------------------------- *)

fun string_of_np (n,p) = 
  "time " ^ its n ^ ", size " ^ its (prog_size p) ^ ": " ^ humanf p 

fun stats_prime dir primesol =
  let 
    val primesol_small = dict_sort (snd_compare prog_compare_size) primesol 
    val primesol_fast = dict_sort (fst_compare Int.compare) primesol 
  in
    writel (dir ^ "/best_small") (map string_of_np primesol_small);
    writel (dir ^ "/best_fast") (map string_of_np primesol_fast)  
  end

fun string_of_snp (seq,(n,p)) = 
  "time " ^ its n ^ ", size " ^ its (prog_size p) ^ ": " ^ humanf p ^ ".   " ^ 
  string_of_seq seq
  
fun stats_hdm dir primesol =
  writel (dir ^ "/best") (map string_of_snp (rev primesol))

(* -------------------------------------------------------------------------
   Files
   ------------------------------------------------------------------------- *)

fun expdir () = selfdir ^ "/exp/" ^ !expname
fun log s = (print_endline s; append_endline (expdir () ^ "/log") s)

fun traindir () = expdir () ^ "/train"
fun searchdir () = expdir () ^ "/search"
fun histdir () = expdir () ^ "/hist"
fun tnn_file ngen = histdir () ^ "/tnn" ^ its ngen
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

fun write_primesol_atomic ngen primesol = 
  let
    val newfile = itsol_file ngen
    val oldfile = newfile ^ "_temp"
  in
    write_primel oldfile primesol;
    OS.FileSys.rename {old = oldfile, new = newfile}
  end

fun read_itsol ngen = read_itprogl (itsol_file ngen)
fun read_primesol ngen = read_primel (itsol_file ngen)

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
   Another syntactic check based on the existence of loops
   ------------------------------------------------------------------------- *) 
  
fun is_bounded (p as Ins (id,argl)) = 
  is_constant p orelse
  (id = 7 andalso is_constant (last argl))
 
fun is_uloop p = case p of
    Ins (9,[p1,p2,p3]) => not (is_bounded p2)
  | Ins (12,[p1,p2]) => not (is_bounded p2)
  | Ins (13,[p1,p2,p3,p4,p5]) => not (is_bounded p3)
  | Ins (15,[p1,p2,p3,p4,p5,p6,p7]) => not (is_bounded p4)
  | _ => false

fun collect_uloop ptop = 
  let 
    val l = ref []
    fun loop (p as Ins (id,argl)) =
      if is_uloop p then l := p :: (!l) else app loop argl
  in
    loop ptop;
    dict_sort prog_compare (!l)
  end

fun merge_sameloop rpl = 
  let 
    val d = ref (dempty (list_compare prog_compare)) 
    fun f (r,p) = 
      let val uloopl = collect_uloop p in
        case dfindo uloopl (!d) of
          SOME (r',p') => if r < r' then d := dadd uloopl (r,p) (!d) else ()
        | NONE => d := dadd uloopl (r,p) (!d) 
      end
  in
    app f rpl;
    map snd (dlist (!d))
  end

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

val extra_flag = ref false
val extra_file = 
  if !local_flag then selfdir ^ "/model/itsol209" else 
  selfdir ^ "/exp/paper-small/hist/itsol20"

fun add_extra () =
  if not (!extra_flag) then [] else 
  let val sol = read_itprogl extra_file in 
    List.concat (map (fn (_,x) => map snd x) sol) 
  end

val merge_flag = ref false

fun trainf_start () =
  if !prime_flag orelse !hadamard_flag then
  let
    val primesol = read_primesol (find_last_itsol ())
    val _ = print_endline ("reading primesol " ^ its (length primesol))
    val rprogl = map snd primesol
    val rprogl' = if !merge_flag then merge_sameloop rprogl else rprogl
    val _ = if !merge_flag 
      then stats_prime (traindir () ^ "/" ^ its (!ngen_glob)) rprogl'
      else ()
    val progl = map snd rprogl'
    val progset = shuffle (mk_fast_set prog_compare (progl @ add_extra ()))
    val _ = print_endline ("programs " ^ its (length progset))
    val ex = create_exl_prime progset
    val _ = print_endline (its (length ex) ^ " examples created")
  in
    (print_endline "exporting training data";
     export_traindata ex;
     print_endline "exporting end")
  end
  else
  let
    val itsol = read_itsol (find_last_itsol ())
    val _ = print_endline ("reading itsol " ^ (its (length itsol)))
    val isolaux = map (fn (a,bl) => (a,map snd bl)) itsol
    val isol = distrib isolaux
    val ex = create_exl (shuffle isol)
    val _ = print_endline (its (length ex) ^ " examples created")
  in
    (print_endline "exporting training data";
     export_traindata ex;
     print_endline "exporting end")
  end

fun trainf_end () =
  let
    (* sml *)  
    val tnnsml_file = tnndir ^ "/out_sml"
    val tnn = read_ctnn (readl tnnsml_file)
    val _ = write_tnn_atomic (!ngen_glob) tnn
    (* openblas *)
    val obfile = histdir () ^ "/ob" ^ its (!ngen_glob)
    val obfile_temp = obfile ^ "_temp"
    val catcmd = "cat ob_fst.c out_ob ob_snd.c > "  
  in
    cmd_in_dir tnndir (catcmd ^ obfile_temp);
    OS.FileSys.rename {old = obfile_temp, new = obfile}
  end


fun wrap_trainf ngen =
  let
    val makefile = !buildheap_dir ^ "/Holmakefile"
    val script1 = !buildheap_dir ^ "/train_start.sml" 
    val script2 = !buildheap_dir ^ "/train_end.sml" 
    val tnnlog_file = tnn_file (!ngen_glob) ^ "_log"
    val sbin = "./tree"
    val preambule = 
      [
       "open rl;",
       "rl.expname := " ^ mlquote (!expname) ^ ";",
       "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir) ^ ";",
       "rl.ngen_glob := " ^ its (!ngen_glob) ^ ";",
       "tnn.dim_glob := " ^ its (!dim_glob) ^ ";",
       "tnn.use_ob := " ^ bts (!use_ob) ^ ";"
       ]
  in
    writel makefile ["INCLUDES = " ^ selfdir]; 
    writel script1 (preambule @ ["trainf_start ();"]);
    writel script2 (preambule @ ["trainf_end ();"]);
    exec_script script1;
    cmd_in_dir tnndir (sbin ^ " > " ^ tnnlog_file);
    exec_script script2
  end

(* -------------------------------------------------------------------------
   Initialize counting tree
   ------------------------------------------------------------------------- *)

fun macro_of_prog_aux (Ins (id,pl)) = 
  id :: List.concat (map macro_of_prog_aux (rev pl));
fun macro_of_prog p = rev (macro_of_prog_aux p);

fun mk_ctree macrol =
  let 
    val ct = ref search.ctempty
    fun loop macro = 
      if null macro then () 
      else (ct := search.cadd macro (!ct); loop (tl macro)) 
    fun f macro = loop (rev macro)
  in
    app f macrol; !ct
  end

fun mk_ctree_sol sol = 
  let 
    val progl = List.concat (map (map snd o snd) sol)
    val macrol = map macro_of_prog progl
  in
    mk_ctree macrol
  end
  
fun init_ct () = 
  if !ngen_glob = 0 orelse not (!simple_flag) then () else
  let 
    val sol = read_itsol (!ngen_glob - 1)
    val ct = mk_ctree_sol sol
  in
    search.ct_glob := ct         
  end   


(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

fun clean_dicts () = 
  (progd := eempty prog_compare; embd := dempty Term.compare)

(* also used in non-cubing *)
fun init_cube () =
  let
    val _ = print_endline "initialization"
    val _ = if !ngen_glob <= 0
            then search.randsearch_flag := true
            else (init_ct (); search.randsearch_flag := false) 
    val _ = use_ob := true
    val _ = noise_flag := false
    (*
            if !ngen_glob mod 2 = 0
            then noise_flag := false
            else (noise_flag := true; noise_coeff_glob := 0.1)
     *)
    val _ = if !ngen_glob = 0 orelse !simple_flag then () 
            else update_fp_op (tnndir ^ "/ob.so")
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
     "tnn.dim_glob := " ^ its (!dim_glob),
     "tnn.use_ob := " ^ bts (!use_ob),
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
    val fileso = tnndir ^ "/ob_online.so"
    val _ = if not (exists_file fileso) 
            then raise ERR "search_target" ""
            else ()
    val _ = if !use_ob then update_fp_op fileso else ()
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
    val leafl = all_leaf tree
    fun f (node,cl,prob) = 
      let fun g (move,r,_) = 
        ((#apply_move game.game) move (#board node), !rtim * prob * r) 
      in
        map g cl
      end
  in
    List.concat (map f leafl)
  end
    
fun start_cube n =
  let    
    val _ = init_ct ()
    val _ = 
      if !ngen_glob = 0 then player_glob := player_random 
      else if !simple_flag then player_glob := search.cplayer (!search.ct_glob)
      else (update_fp_op (tnndir ^ "/ob.so"); player_glob := player_wtnn_cache)
    val _ = noise_flag := false
            (*
            if !ngen_glob mod 2 = 0
            then noise_flag := false
            else (noise_flag := true; noise_coeff_glob := 0.1)
             *)
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
     "tnn.dim_glob := " ^ its (!dim_glob),
     "tnn.use_ob := " ^ bts (!use_ob),
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
  end;
  
fun cube () = 
  let
    val tree = start_cube (ncore * 2)
    val l1 = sort_cube (regroup_cube [] 0.0 (shuffle (get_boardsc tree)))
  in
    smlParallel.parmap_queue_extern ncore cubespec () l1
  end;


(* 
load "rl"; open rl mcts aiLib kernel;
rtim := 200.0;
PolyML.print_depth 0;
val (_,t1) = add_time test_cube 1;
val (_,t2) = add_time test_cube 2;
val (_,t3) = add_time test_cube 3;
PolyML.print_depth 40;
t1; t2; t3;
*)

(* -------------------------------------------------------------------------
   Searching for prime approximations
   ------------------------------------------------------------------------- *)

type primesol = seq * (int * prog)

fun search_prime () btiml =
  (
  search.randsearch_flag := (!ngen_glob = 0); 
  checkinit_prime ();
  app (fn (board,tim) => search.search_board (0, tim) board) btiml;
  checkfinal_prime ()
  )

val primespec : (unit, (prog list * real) list, primesol list) extspec =
  {
  self_dir = selfdir,
  self = "rl.primespec",
  parallel_dir = selfdir ^ "/cube_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "rl.expname := " ^ mlquote (!expname),
     "rl.ngen_glob := " ^ its (!ngen_glob),
     "tnn.dim_glob := " ^ its (!dim_glob),
     "tnn.use_ob := " ^ bts (!use_ob),
     "game.time_opt := " ^ string_of_timeo (),
     "rl.init_cube ()"] 
    ^ ")"),
  function = search_prime,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_proglrl,
  read_arg = read_proglrl,
  write_result = write_primel,
  read_result = read_primel
  }

fun prime () = 
  let
    val tree = start_cube (ncore * 2)
    val l1 = sort_cube (regroup_cube [] 0.0 (shuffle (get_boardsc tree)))
  in
    smlParallel.parmap_queue_extern ncore primespec () l1
  end


(* -------------------------------------------------------------------------
   Searching for hadamard matrices
   ------------------------------------------------------------------------- *)

fun search_hdm () btiml =
  (
  search.randsearch_flag := (!ngen_glob = 0); 
  checkinit_hdm ();
  app (fn (board,tim) => search.search_board (0, tim) board) btiml;
  checkfinal_hdm ()
  )

val hdmspec : (unit, (prog list * real) list, primesol list) extspec =
  {
  self_dir = selfdir,
  self = "rl.hdmspec",
  parallel_dir = selfdir ^ "/cube_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "rl.expname := " ^ mlquote (!expname),
     "rl.ngen_glob := " ^ its (!ngen_glob),
     "tnn.dim_glob := " ^ its (!dim_glob),
     "tnn.use_ob := " ^ bts (!use_ob),
     "game.time_opt := " ^ string_of_timeo (),
     "rl.init_cube ()"] 
    ^ ")"),
  function = search_hdm,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_proglrl,
  read_arg = read_proglrl,
  write_result = write_primel,
  read_result = read_primel
  }

fun hdm () = 
  let
    val tree = start_cube (ncore * 2)
    val l1 = sort_cube (regroup_cube [] 0.0 (shuffle (get_boardsc tree)))
  in
    smlParallel.parmap_queue_extern ncore hdmspec () l1
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

fun string_of_tp (t,p) =
  "size " ^ its (prog_size p) ^ ", time " ^ its t ^ ": " ^ humanf p

fun string_of_itprog (i,tpl) = 
  "A" ^ its i ^ ": " ^ string_of_seq (valOf (Array.sub (oseq,i))) ^ "\n" ^
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

fun mk_partial (anum,p) = 
  let fun f x = (length (valOf (Array.sub (oseq, x))), NONE) in
    (anum,[(f anum,p)])
  end
  
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

fun worst_prime bl = 
  let
    val (good,tot) = (ref 1, ref 1) 
    val worst = ref 1.0
    fun f b = 
      (if b then incr good else (); 
       incr tot;
       let val proba = int_div (!good) (!tot) in 
         if proba < !worst then worst := proba else () end)
  in
    app f bl;
    !worst
  end

fun number_of_errors (bn,badl) = (997 - bn) + length badl

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
    val _ =
      if !ngen_glob = 0 orelse !simple_flag then () else
      let 
        val tnngen = find_last_ob ()
        val obfile = histdir () ^ "/ob" ^ its tnngen
        val obc = tnndir ^ "/ob.c"
        val cpcmd = String.concatWith " " ["cp",obfile,obc]
      in
        cmd_in_dir tnndir cpcmd;
        cmd_in_dir tnndir "sh compile_ob.sh ob.c"
      end
    in
      if !prime_flag then 
      let 
        val (primesoll,t) = add_time prime ()
        val _ = log ("search time: " ^ rts_round 6 t)
        val oldprimesol = if ngen = 0 then [] else read_primesol (ngen - 1)
        val newprimesol = 
          merge_primesol (List.concat (oldprimesol :: primesoll))
        val allprog = map (snd o snd) newprimesol
        val _ = log ("programs: " ^ (its (length allprog)))
        val sizel = dict_sort Int.compare (map prog_size allprog)
        val _ = log ("average best size: " ^ String.concatWith " "
          (map (rts_round 2 o average_int) 
           [sizel, first_n 1000 sizel, first_n 100 sizel, first_n 10 sizel]))
        val speedl = dict_sort Int.compare (map (fst o snd) newprimesol)  
        val _ = log ("average best speed: " ^  String.concatWith " "
          (map (rts_round 2 o average_int) 
          [speedl, first_n 1000 speedl, first_n 100 speedl, first_n 10 speedl]))
      in  
        write_primesol_atomic ngen newprimesol;
        stats_prime (!buildheap_dir) (map snd newprimesol)
      end
      else if !hadamard_flag then 
      let 
        val (primesoll,t) = add_time hdm ()
        val _ = log ("search time: " ^ rts_round 6 t)
        val oldprimesol = if ngen = 0 then [] else read_primesol (ngen - 1)
        val newprimesol = merge_hdmsol (List.concat (oldprimesol :: primesoll))
        val allprog = map (snd o snd) newprimesol
        val _ = log ("programs: " ^ (its (length allprog)))
        val sizel = dict_sort Int.compare (map prog_size allprog)
      in  
        write_primesol_atomic ngen newprimesol;
        stats_hdm (!buildheap_dir) newprimesol
      end
      else
      let
        val (itsoll,t) = 
          if !notarget_flag orelse !simple_flag then add_time cube ()
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

fun rl_search_simple_aux ngen = 
  (
  rl_search_only ngen;
  PolyML.fullGC ();
  if isSome (!maxgen) andalso ngen >= valOf (!maxgen) then () else 
  rl_search_simple_aux (ngen + 1)
  )

fun rl_search_simple () =
  let 
    val _ = ignore (mk_dirs ())  
    val n = ((find_last_itsol () + 1) handle HOL_ERR _ => 0)
  in
    rl_search_simple_aux n
  end

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

fun wait_itsol () = 
  if can find_last_itsol () then () else 
  (OS.Process.sleep (Time.fromReal 1.0); wait_itsol ())

fun rl_train_cont () = 
  (
  ignore (mk_dirs ());
  if can find_last_itsol () 
  then () 
  else (print_endline "waiting for itsol"; wait_itsol ())
  ;
  rl_train_only ((find_last_ob () + 1) handle HOL_ERR _ => 0); 
  rl_train_cont ();
  PolyML.fullGC ()
  )

end (* struct *)

