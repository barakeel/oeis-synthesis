structure rl :> rl =
struct

open HolKernel Abbrev boolLib aiLib smlParallel smlExecScripts 
  mlTreeNeuralNetwork mcts kernel human bloom exec game check tnn knn
  

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
val rtim_init = ref
  (valOf (Real.fromString (dfind "rtim_init" configd)) 
   handle NotFound => 7200.0)   
   
val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)
val ntarget = (string_to_int (dfind "ntarget" configd) handle NotFound => 32)
val ntarget_init = (string_to_int (dfind "ntarget_init" configd) 
  handle NotFound => 32)
val maxgen = ref NONE
val tnndir = selfdir ^ "/tnn_in_c"
val modeldir = selfdir ^ "/model"

(* -------------------------------------------------------------------------
   Files
   ------------------------------------------------------------------------- *)

fun expdir () = selfdir ^ "/exp/" ^ !expname
fun log s = (print_endline s; append_endline (expdir () ^ "/log") s)

fun exdir () = expdir () ^ "/ex"
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

(* pgen experiment *)
fun read_pgensol ngen = read_pgen (itsol_file ngen)
fun write_pgensol_atomic ngen pgensol = 
  let
    val newfile = itsol_file ngen
    val oldfile = newfile ^ "_temp"
  in
    write_pgen oldfile pgensol;
    OS.FileSys.rename {old = oldfile, new = newfile}
  end  

(* ramsey experiment *)
fun read_ramseysol ngen = read_ramseyl (itsol_file ngen)

fun write_ramseysol_atomic ngen ramseysol = 
  let
    val newfile = itsol_file ngen
    val oldfile = newfile ^ "_temp"
  in
    write_ramseyl oldfile ramseysol;
    OS.FileSys.rename {old = oldfile, new = newfile}
  end

(* hanabi experiment *)
fun read_hanabisol ngen = read_hanabil (itsol_file ngen)

fun write_hanabisol_atomic ngen hanabisol = 
  let
    val newfile = itsol_file ngen
    val oldfile = newfile ^ "_temp"
  in
    write_hanabil oldfile hanabisol;
    OS.FileSys.rename {old = oldfile, new = newfile}
  end
  
(* arcagi experiment *)
fun read_arcagisol ngen = read_arcagil (itsol_file ngen)

fun write_arcagisol_atomic ngen arcagisol = 
  let
    val newfile = itsol_file ngen
    val oldfile = newfile ^ "_temp"
  in
    write_arcagil oldfile arcagisol;
    OS.FileSys.rename {old = oldfile, new = newfile}
  end  
  

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

val extra_file = selfdir ^ "/model/itsol209"

fun add_extra () =
  if not (!extra_flag) then [] else 
  let val sol = read_itprogl extra_file in 
    List.concat (map (fn (_,x) => map snd x) sol) 
  end

fun trainf_pgen datadir pid =
  let
    val pgensol = read_pgensol (find_last_itsol ())
    val progl = map fst pgensol
    val progset = shuffle (mk_fast_set prog_compare progl)
    val _ = print_endline ("programs " ^ its (length progset))
    val ex = create_exl_progset progset
    val nex = length ex
    val _ = print_endline (its nex ^ " examples created")
  in
    if length ex < 10 then raise ERR "too few examples" "" else
    export_traindata datadir num_epoch learning_rate dim_glob ex
  end

fun trainf_ramsey datadir pid =
  let
    val ramseysol = read_ramseysol (find_last_itsol ())
    val progl = map (snd o fst) ramseysol
    val progset = shuffle (mk_fast_set prog_compare progl)
    val _ = print_endline ("programs " ^ its (length progset))
    val ex = create_exl_progset progset
    val nex = length ex
    val _ = print_endline (its (length ex) ^ " examples created")
  in
    if nex < 10 then raise ERR "too few examples" "" else
    export_traindata datadir num_epoch learning_rate dim_glob ex
  end
  
fun trainf_hanabi datadir pid =
  let
    val hanabisol = read_hanabisol (find_last_itsol ())
    val progl = map (snd o fst) hanabisol
    val progset = shuffle (mk_fast_set prog_compare progl)
    val _ = print_endline ("programs " ^ its (length progset))
    val ex = create_exl_progset progset
    val nex = length ex
    val _ = print_endline (its (length ex) ^ " examples created")
  in
    if nex < 10 then raise ERR "too few examples" "" else
    export_traindata datadir num_epoch learning_rate dim_glob ex
  end
  
fun trainf_arcagi datadir pid =
  let
    val arcagisol = read_arcagisol (find_last_itsol ())
    val progl = map #2 arcagisol
    val progset = shuffle progl
    val _ = print_endline ("programs " ^ its (length progset))
    val ex = create_exl_progset progset
    val nex = length ex
    val _ = print_endline (its (length ex) ^ " examples created")
  in
    if nex < 10 then raise ERR "too few examples" "" else
    export_traindata datadir num_epoch learning_rate dim_glob ex
  end  
  
  
fun trainf_tnn datadir pid =
  let
    val itsol = read_itsol (find_last_itsol ()) @ 
       (if !extra_flag then read_itprogl extra_file else [])
    val _ = print_endline ("reading itsol " ^ (its (length itsol)))
    val isol0 = distrib (map (fn (a,bl) => (a,map snd bl)) itsol)
    val isol =
      let 
        val progl = mk_fast_set prog_compare_size (map snd isol0)
        val progsel =
          if pid <= 1 andalso !wrat_flag  
            then
              let val progl' = filter (contain_opers "while2") progl in
                get_cluster (length progl' + 200) progl (random_elem progl')
              end                
          else if !select_cluster 
            then random_cluster select_number progl
          else if !select_random
            then random_subset select_number progl
          else progl
        val d = enew prog_compare progsel
      in
        filter (fn (i,p) => emem p d) isol0 
      end
    val ex = create_exl (shuffle isol)
    val nex = length ex
    val _ = print_endline (its nex ^ " examples created")
    val newex = ex
  in
    if nex < 10 then raise ERR "too few examples" "" else
    export_traindata datadir num_epoch learning_rate dim_glob newex
  end

(*
load "kernel"; open kernel aiLib;
val exdir = selfdir ^ "/exp/smartselect/ex";
val filel = map (fn x => exdir ^ "/" ^ x) (listDir exdir);
val l2 = map_assoc read_seqprog filel;
fun f (a,c) = 
  let val a1 = (string_to_int o snd o split_string "exA" o OS.Path.file) a in
    (a1,c)
  end;
val isol0 = map f l2;  
val isol1 = distrib (map (fn (a,bl) => (a,map snd bl)) isol0);

kernel.expname := "smartselect";

val tnndir = selfdir ^ "/tnn_in_c"
val dir = selfdir ^ "/exp/smartselect/selector3";
val obfile = dir ^ "/ob.c"
val obfst = tnndir ^ "/ob_fst.c"
val obsnd = tnndir ^ "/ob_snd.c";
val catcmd = String.concatWith " " ["cat",obfst,"out_ob",obsnd,">",obfile];
val _ = cmd_in_dir dir catcmd;
val _ = cmd_in_dir tnndir ("sh compile_ob.sh " ^ obfile);


load "rl"; open rl;
kernel.expname := "smartselect";
trainf_isol dir isol1;
*)

fun trainf_start pid =
  let 
    val execdir = tnndir ^ "/para/" ^ its pid
    val datadir = execdir ^ "/data"
    val _ = app mkDir_err [tnndir ^ "/para", execdir, datadir]
    val _ = cmd_in_dir tnndir ("cp tree " ^ execdir)
    val _ = print_endline "exporting training data"
  in
    (* if !smartselect_flag then ... else ... *)
    if !pgen_flag then trainf_pgen datadir pid
    else if !ramsey_flag then trainf_ramsey datadir pid    
    else if !hanabi_flag orelse !rams_flag then trainf_hanabi datadir pid
    else if !arcagi_flag then trainf_arcagi datadir pid  
    else trainf_tnn datadir pid
    ;
    print_endline "exporting end"
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
       "kernel.expname := " ^ mlquote (!expname) ^ ";",
       "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir) ^ ";",
       "kernel.ngen_glob := " ^ its (!ngen_glob) ^ ";"
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
   Standalone training loop (for training set generators)
   ------------------------------------------------------------------------- *)

fun trainf_isol dir isol =
  let
    val tnndir = selfdir ^ "/tnn_in_c"
    val datadir = dir ^ "/data"
    val _ = app mkDir_err [dir,datadir]
    val ex = create_exl (shuffle isol)
    val nex = length ex
    val _ = print_endline (its nex ^ " examples created")
    val _ = export_traindata datadir num_epoch learning_rate dim_glob ex
    val _ = print_endline (its nex ^ " examples exported: " ^ datadir)
    val _ = cmd_in_dir tnndir ("cp tree " ^ dir)
    val logfile = dir ^ "/log"
    val (_,t) = add_time (cmd_in_dir dir) ("./tree" ^ " > " ^ logfile)
    val _ = print_endline ("train time: " ^ rts_round 4 t)
    val obfile = dir ^ "/ob.c"
    val obfst = tnndir ^ "/ob_fst.c"
    val obsnd = tnndir ^ "/ob_snd.c"
    val catcmd = String.concatWith " " ["cat",obfst,"out_ob",obsnd,">",obfile]
    val _ = cmd_in_dir dir catcmd
    val _ = cmd_in_dir tnndir ("sh compile_ob.sh " ^ obfile)
  in
    ()
  end
  
fun train_smartselect_loop () =
  let
    val exdirloc = exdir ()
    val filel = map (fn x => exdirloc ^ "/" ^ x) 
      (random_subset 256 (listDir exdirloc)) 
      (* otherwise training takes too long *)
    val l2 = map_assoc read_seqprog filel
    fun f (a,c) = 
      let val a1 = 
        (string_to_int o snd o split_string "exA" o OS.Path.file) a 
      in
        (a1,c)
      end
    val isol0 = map f l2;  
    val isol1 = distrib (map (fn (a,bl) => (a,map snd bl)) isol0)
    val dir = traindir () ^ "/" ^ its (!ngen_glob)
  in
    trainf_isol dir isol1;
    cmd_in_dir dir ("mv ob.so" ^ " ob" ^ its (!ngen_glob) ^ "_0.so");
    writel_atomic (histdir () ^ "/ob" ^ its (!ngen_glob)) [];
    incr ngen_glob;
    train_smartselect_loop ()
  end
  
fun train_smartselect ngen = 
  (
  ngen_glob := ngen;
  train_smartselect_loop ()
  )

(* -------------------------------------------------------------------------
   Standalone training
   ------------------------------------------------------------------------- *)

fun train_pl dir pl =
  let
    fun log s = (print_endline s; append_endline (dir ^ "/log") s) 
    val tnndir = selfdir ^ "/tnn_in_c"
    val expdir = selfdir ^ "/exp"
    val datadir = dir ^ "/data"
    val _ = app mkDir_err [expdir,dir,datadir]
    val ex = create_exl_progset pl
    val nex = length ex
    val _ = log (its nex ^ " examples created")
    val _ = export_traindata datadir num_epoch learning_rate dim_glob ex
    val _ = log (its nex ^ " examples exported: " ^ datadir)
    val _ = cmd_in_dir tnndir ("cp tree " ^ dir)
    val logfile = dir ^ "/log"
    val (_,t) = add_time (cmd_in_dir dir) ("./tree" ^ " > " ^ logfile)
    val _ = log ("train time: " ^ rts_round 4 t)
    val obfile = dir ^ "/ob.c"
    val obfst = tnndir ^ "/ob_fst.c"
    val obsnd = tnndir ^ "/ob_snd.c"
    val catcmd = String.concatWith " " ["cat",obfst,"out_ob",obsnd,">",obfile]
    val _ = cmd_in_dir dir catcmd
    val _ = cmd_in_dir tnndir ("sh compile_ob.sh " ^ obfile)
  in
    ()
    
  end

(* -------------------------------------------------------------------------
   Looping search and training for program generators
   ------------------------------------------------------------------------- *)

fun init_train_pg () = 
  let
    val pgenl = read_progl (selfdir ^ "/filterunique/pgen")
    val dir = selfdir ^ "/filterunique_train"
  in
    train_pl dir pgenl
  end

fun train_pg (expname,ngen) pgenl = 
  let 
    val expdir = selfdir ^ "/exp"
    val namedir = expdir ^ "/" ^ expname
    val traindir = namedir ^ "/train"
    val dir = traindir ^ "/" ^ its ngen
    val _ = app mkDir_err [expdir,namedir,traindir,dir]  
  in
    train_pl dir pgenl
  end
  
fun rl_pg_search expname ngen =  
  let
    (* todo: make the set of examples updatable *)
    val pex0 = read_itprogl (selfdir ^ "/model/nmt504")
    val pex1 = 
      let fun f (anum,tpl) = 
        (anum,hd (dict_sort prog_compare_size (map snd tpl)))
      in
        map f pex0  
      end
    val expdir = selfdir ^ "/exp"
    val namedir = expdir ^ "/" ^ expname
    val traindir = namedir ^ "/train"
    val _ = app mkDir_err [expdir,namedir,traindir]  
    fun log s = (print_endline s; append_endline (namedir ^ "/log") s)
    val _ = log ("Generation " ^ its ngen)
    val _ = log "infer"
    val gl = 
      if !prnnsum_flag andalso ngen <= 0 
      then search.random_pgenl (int_pow 2 20) 20.0
      else 
        let val fileso = if ngen <= 0 
                 then selfdir ^ "/filterunique_train/ob.so" 
                 else traindir ^ "/" ^ its (ngen - 1) ^ "/ob.so"
        in
          if exists_file fileso 
          then search.infer_pgenl fileso (int_pow 2 20) 130.0
          else raise ERR "rl_pg_search" fileso
        end
    val _ = log "search"
    val gex = search.compete_pgenl (expname,ngen) pex1 gl
    val _ = log "train"
    val () = train_pg (expname,ngen) gex
  in
    rl_pg_search expname (ngen + 1)
  end

fun rl_pg_train expname ngen =  
  let
    val expdir = selfdir ^ "/exp"
    val namedir = expdir ^ "/" ^ expname
    val searchdir = namedir ^ "/search"
    val _ = app mkDir_err [expdir,namedir,searchdir]
    fun log s = (print_endline s; append_endline (namedir ^ "/log") s) 
    val dir = searchdir ^ "/" ^ its ngen
    val exfile = dir ^ "/ex"
    val _ = if exists_file exfile then () else raise ERR "rl_pg_train" 
      "need example file in search directory"  
    val ex = read_progl exfile
    val _ = log "training"
    val () = train_pg (expname,ngen) ex
  in
    rl_pg_search expname (ngen + 1)
  end


(* load "rl"; rl.rl_pg_search "pgen1" 0; *)


(* -------------------------------------------------------------------------
   Parallel search
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
  
fun find_train_multi ns =
  let 
    fun f i = traindir () ^ "/" ^ ns ^ "/ob" ^ ns ^ "_" ^ its i ^ ".so"
    fun loop i = if exists_file (f i) then loop (i+1) else i 
  in  
    loop 0
  end
  
fun load_ob () =
  let 
    val ns = its (find_last_ob ()) 
    val inferred_train_multi = find_train_multi ns
    val _ = if inferred_train_multi <= 0 then raise ERR "load_ob" "" else ()
    val suffix = its (random_int (0,inferred_train_multi - 1))
    val fileso = traindir () ^ "/" ^ ns ^ "/ob" ^ ns ^ "_" ^ suffix ^ ".so"
  in
    print_endline ("loading " ^ fileso);
    update_fp_op fileso dim_glob
  end
    

(* Loading OpenBlas TNN via the FFI *)
fun auto_load_ob () =
  let
    val _ = search.randsearch_flag := not (can find_last_ob ())
    val _ = if !search.randsearch_flag 
            then print_endline "random search"
            else print_endline "tnn-guided search"
    val _ = halfnoise ()
    val _ = if (!search.randsearch_flag) then () else load_ob ()   
  in
    ()
  end

fun search () targetn =
  let 
    val _ = print_endline "search start" 
    val rtimloc = if !ngen_glob <= 0 then !rtim_init else !rtim
  in
    if !beam_flag andalso !ngen_glob > 0
      then search.beamsearch ()
    else (
         select_random_target (); 
         search.search (!nvis,rtimloc); 
         checkfinal ()
         )
  end

(* 
load "rl"; open rl;
search.randsearch_flag := true;
search.search (0,60.0);
val sol = check.checkfinal ();

*)

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
     "kernel.expname := " ^ mlquote (!expname),
     "kernel.ngen_glob := " ^ its (!ngen_glob),
     "game.time_opt := " ^ string_of_timeo (),
     "rl.auto_load_ob ()"] 
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
   
fun search_target target = raise ERR "search_target" "not supported anymore"
(* 
let
  val _ = clean_dicts ()
  val fileso = modeldir ^ "/ob_online.so"
  val _ = if not (exists_file fileso) 
          then raise ERR "search_target" ""
          else ()
  val _ = update_fp_op fileso dim_glob
  val _ = player_glob := player_wtnn_cache
  val _ = target_glob := target
  val _ = online_flag := true
  val tree = starting_tree (mctsobj ()) []
  val (newtree,t) = add_time (mcts (mctsobj ())) tree
in
  online_flag := false; clean_dicts (); NONE
end
handle ResultP p => SOME p
*)

(* -------------------------------------------------------------------------
   Variant of the search function for cube and conquer
   ------------------------------------------------------------------------- *)

fun get_boardsc tree = 
  let 
    val maxprob = 1.0 / Real.fromInt ncore
    val leafl = all_leaf tree
    val rtimloc = if !ngen_glob <= 0 then !rtim_init else !rtim
    fun f (node,cl,prob) = 
      let fun g (move,r,_) = 
        let val r' = if prob * r > maxprob then maxprob else prob * r in
          ((#apply_move game.game) move (#board node), rtimloc * r')
        end 
      in
        map g cl
      end
  in
    List.concat (map f leafl)
  end
    
fun start_cube n =
  let    
    val _ = if !ngen_glob <= 0 then () else load_ob ()
    val _ = if !ngen_glob <= 0 
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
     "kernel.expname := " ^ mlquote (!expname),
     "kernel.ngen_glob := " ^ its (!ngen_glob),
     "rl.auto_load_ob ()"] 
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
   Search: pgen experiment
   ------------------------------------------------------------------------- *)

fun search_pgen () btiml =
  (
  search.randsearch_flag := (!ngen_glob = 0); 
  checkinit_pgen ();
  app (fn (board,tim) => search.search_board (0, tim) board) btiml;
  checkfinal_pgen ()
  )

val pgenspec : (unit, (prog list * real) list, pgen list) extspec =
  {
  self_dir = selfdir,
  self = "rl.pgenspec",
  parallel_dir = selfdir ^ "/cube_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "kernel.expname := " ^ mlquote (!expname),
     "kernel.ngen_glob := " ^ its (!ngen_glob),
     "rl.auto_load_ob ()"] 
    ^ ")"),
  function = search_pgen,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_proglrl,
  read_arg = read_proglrl,
  write_result = write_pgen,
  read_result = let fun f file = 
    (cmd_in_dir selfdir ("cp " ^ file ^ " " ^ mergedir ^ "/" ^ its (!mergen)); 
     incr mergen; 
     [])
    in f end
  }

fun pgen () = 
  let
    val tree = start_cube (ncore * 2)
    val l1 = sort_cube (regroup_cube [] 0.0 (shuffle (get_boardsc tree)))
  in
    smlParallel.parmap_queue_extern ncore pgenspec () l1
  end

(* -------------------------------------------------------------------------
   Searching for Ramsey graph
   ------------------------------------------------------------------------- *)

fun search_ramsey_branchl () btiml =
  (
  search.randsearch_flag := (!ngen_glob = 0); 
  checkinit_ramsey ();
  app (fn (board,tim) => search.search_board (0, tim) board) btiml;
  checkfinal_ramsey ()
  )

val ramseyspec : (unit, (prog list * real) list, ramsey list) extspec =
  {
  self_dir = selfdir,
  self = "rl.ramseyspec",
  parallel_dir = selfdir ^ "/cube_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "kernel.expname := " ^ mlquote (!expname),
     "kernel.ngen_glob := " ^ its (!ngen_glob),
     "game.time_opt := " ^ string_of_timeo (),
     "rl.auto_load_ob ()"]
    ^ ")"),
  function = search_ramsey_branchl,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_proglrl,
  read_arg = read_proglrl,
  write_result = write_ramseyl,
  read_result = let fun f file = 
    (cmd_in_dir selfdir ("cp " ^ file ^ " " ^ mergedir ^ "/" ^ its (!mergen)); 
     incr mergen; 
     [])
    in f end
  }

fun search_ramsey () = 
  let
    val tree = start_cube (ncore * 8)
    val l1 = 
      [([],10.0)] :: 
      sort_cube (regroup_cube [] 0.0 (shuffle (get_boardsc tree)))
  in
    smlParallel.parmap_queue_extern ncore ramseyspec () l1
  end

fun string_of_ramseysol ((regsc,p),(sc,humsc,h,t)) = 
  "sc: " ^ its sc ^ ", " ^
  "size: " ^ its (prog_size p) ^ ", " ^
  "hash: " ^ its h ^ ": " ^
  humanf p
  
fun stats_ramsey dir ramseysol =
  writel (dir ^ "/best") (map string_of_ramseysol (rev ramseysol))

(* -------------------------------------------------------------------------
   Searching for Hanabi strategy
   ------------------------------------------------------------------------- *)

fun search_hanabi_branchl () btiml =
  (
  search.randsearch_flag := (!ngen_glob = 0); 
  checkinit_hanabi ();
  app (fn (board,tim) => search.search_board (0, tim) board) btiml;
  checkfinal_hanabi ()
  )

val hanabispec : (unit, (prog list * real) list, hanabi list) extspec =
  {
  self_dir = selfdir,
  self = "rl.hanabispec",
  parallel_dir = selfdir ^ "/cube_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "kernel.expname := " ^ mlquote (!expname),
     "kernel.ngen_glob := " ^ its (!ngen_glob),
     "game.time_opt := " ^ string_of_timeo (),
     "rl.auto_load_ob ()"]
    ^ ")"),
  function = search_hanabi_branchl,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_proglrl,
  read_arg = read_proglrl,
  write_result = write_hanabil,
  read_result = let fun f file = 
    (cmd_in_dir selfdir ("cp " ^ file ^ " " ^ mergedir ^ "/" ^ its (!mergen)); 
     incr mergen; 
     [])
    in f end
  }

fun search_hanabi () = 
  let
    val tree = start_cube (ncore * 8)
    val l1 = 
      [([],10.0)] :: 
      sort_cube (regroup_cube [] 0.0 (shuffle (get_boardsc tree)))
  in
    smlParallel.parmap_queue_extern ncore hanabispec () l1
  end

fun string_of_hanabisol ((sc,p),h) = String.concatWith ", "
  ["sc: " ^ its sc, "size: " ^ its (prog_size p), human_trivial p]

fun stats_hanabi dir hanabisol =
  writel (dir ^ "/best") (map string_of_hanabisol (rev hanabisol))


(* -------------------------------------------------------------------------
   Searching for arcagi programs
   ------------------------------------------------------------------------- *)

fun search_arcagi_ex () exi =
  let 
    val _ = search.randsearch_flag := (!ngen_glob = 0)
    val _ = checkinit_arcagi ()
    val _ = print_endline ("search start on example " ^ (its exi))
    val rtimloc = if !ngen_glob <= 0 then !rtim_init else !rtim
    val _ = arcagi.exi_glob := exi
    val _ = arcagi.ex_glob := Vector.sub (!arcagi.trainex_glob, exi)
  in
    (
    search.search (!nvis,rtimloc);
    checkfinal_arcagi ()
    )
  end

fun write_int file i = writel file [its i]
fun read_int file = string_to_int (hd (readl file))


val arcagispec : (unit, int, arcagi list) extspec =
  {
  self_dir = selfdir,
  self = "rl.arcagispec",
  parallel_dir = selfdir ^ "/cube_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "kernel.expname := " ^ mlquote (!expname),
     "kernel.ngen_glob := " ^ its (!ngen_glob),
     "arcagi.read_trainex ()",
     "rl.auto_load_ob ()"]
    ^ ")"),
  function = search_arcagi_ex,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_int,
  read_arg = read_int,
  write_result = write_arcagil,
  read_result = read_arcagil
  }

fun search_arcagi () = 
  let
    val _ = arcagi.read_trainex ()
    val n = Vector.length (!arcagi.trainex_glob)
    val l = List.tabulate (n,I)
    val arcagill = smlParallel.parmap_queue_extern ncore arcagispec () l
  in
    List.concat arcagill
  end

fun string_of_arcagisol (exi,p,b,sc) = String.concatWith ", "
  ["ex: " ^ its exi, "solved: " ^ bts b, "score: " ^ its sc,
   "size: " ^ its (prog_size p), "prog: " ^ human_trivial p]

fun stats_arcagi dir arcagisol =
  writel (dir ^ "/stats") (map string_of_arcagisol arcagisol)


(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun compute_freq f sol1 =
  let val freql = dlist 
    (count_dict (dempty prog_compare) (List.concat (map f sol1)))
  in
    dict_sort compare_imax (filter (fn x => snd x >= 10) freql)
  end

fun human_progfreq (p,freq) = 
  its freq  ^ " : " ^ humanf p ^ " : " ^ gpt_of_prog p

val abillion = 1000 * 1000 * 1000

fun string_of_tp (t,p) =
  "size " ^ its (prog_size p) ^ ", " ^
  (
  if !partial_flag andalso t >= abillion
  then ("correct " ^ its (abillion + 10000 - t)) 
  else "time " ^ its t
  )
  ^ " : " ^ humanf p ^ " : " ^ gpt_of_prog p

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

(* pgen statistics *)
fun string_of_pgensol (ptop,ipl) = 
  let fun f (i,p) = 
    "A" ^ its i ^ ": " ^ string_of_seq (valOf (Array.sub (oseq,i))) ^ "\n" ^
    humanf p
  in
    "cover: " ^ its (length ipl) ^ ", " ^
    "size: " ^ its (prog_size ptop) ^ ", " ^    
    humanf ptop ^ "\n" ^
    String.concatWith "\n" (map f ipl) 
  end
  
fun stats_pgen dir pgensol =
  writel (dir ^ "/stats") (map string_of_pgensol (rev pgensol))

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_search_only_default ngen =
  let
    val targetil = List.tabulate
      (if ngen <= 0 then ntarget_init else ntarget,I)
    val (itsoll,t) = 
      if !notarget_flag 
      then add_time cube ()
      else add_time (parmap_queue_extern ncore parspec ()) targetil
    val _ = log ("search time: " ^ rts_round 6 t)
    val _ = log ("average number of solutions per search: " ^
                  rts_round 2 (average_int (map length itsoll)))
    val olditsol = if ngen = 0 then [] else read_itsol (ngen - 1)
    val newitsol = merge_itsol (List.concat (olditsol :: itsoll))
    val _ = log ("solutions: " ^ (its (length newitsol)))
    val allprog = List.concat (map (map snd o snd) newitsol)
    val alltime = List.concat (map (map fst o snd) newitsol)
    val _ = log ("programs: " ^ (its (length allprog)))
    val _ = log ("average size: " ^ rts_round 2 
      (average_int (map prog_size allprog)))
    val _ = log ("average time: " ^ rts_round 2 (average_int alltime))
    val _ = log ("diff: " ^ its (length newitsol - length olditsol))
    val _ = write_itsol_atomic ngen newitsol
  in
    stats_ngen (!buildheap_dir) ngen
  end
  
fun rl_search_only_pgen ngen =
  let 
    val _ = init_merge ()
    val (pgensol,t) = add_time pgen ()
    val _ = log ("search time: " ^ rts_round 6 t)
    val oldfileo = if ngen = 0 then NONE else SOME (itsol_file (ngen - 1))
    val newpgensol = merge_pgen oldfileo
    val _ = init_merge ()
    val _ = log ("pgen solutions: " ^ (its (length newpgensol)))
  in 
    write_pgensol_atomic ngen newpgensol;
    stats_pgen (!buildheap_dir) newpgensol
  end

fun rl_search_only_ramsey ngen =
  let 
    val _ = init_merge ()
    val (ramseysol,t) = add_time search_ramsey ()
    val _ = log ("search time: " ^ rts_round 6 t)
    val oldfileo = if ngen = 0 then NONE else SOME (itsol_file (ngen - 1))
    val newramseysol = merge_ramsey oldfileo
    val _ = init_merge ()
    val _ = log ("ramsey solutions: " ^ (its (length newramseysol)))
  in 
    write_ramseysol_atomic ngen newramseysol;
    stats_ramsey (!buildheap_dir) newramseysol
  end
  
fun rl_search_only_hanabi ngen =
  let 
    val _ = init_merge ()
    val (hanabisol,t) = add_time search_hanabi ()
    val _ = log ("search time: " ^ rts_round 6 t)
    val oldfileo = if ngen = 0 then NONE else SOME (itsol_file (ngen - 1))
    val newhanabisol = merge_hanabi oldfileo
    val _ = init_merge ()
    val _ = log ("hanabi solutions: " ^ (its (length newhanabisol)))
  in 
    write_hanabisol_atomic ngen newhanabisol;
    stats_hanabi (!buildheap_dir) newhanabisol
  end
  
fun rl_search_only_arcagi ngen =
  let 
    val (arcagisol,t) = add_time search_arcagi ()
    val _ = log ("search time: " ^ rts_round 6 t)
    val oldfileo = if ngen = 0 then NONE else SOME (itsol_file (ngen - 1))
    val newarcagisol = merge_arcagi arcagisol oldfileo
    val actualsol = filter (fn (a,b,c,d) => c) newarcagisol
    val _ = log ("arcagi solutions: " ^ its (length actualsol))
  in 
    write_arcagisol_atomic ngen newarcagisol;
    stats_arcagi (!buildheap_dir) newarcagisol
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
  in
    if !pgen_flag then rl_search_only_pgen ngen
    else if !ramsey_flag then rl_search_only_ramsey ngen
    else if !hanabi_flag orelse !rams_flag then rl_search_only_hanabi ngen
    else if !arcagi_flag then rl_search_only_arcagi ngen
    else rl_search_only_default ngen
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


fun rl_search_cont_nowait () = 
  (
  ignore (mk_dirs ());
  let val n = ((find_last_itsol () + 1) handle HOL_ERR _ => 0) in
    rl_search_only n
  end;
  rl_search_cont_nowait ();
  PolyML.fullGC ()
  )

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

(*
load "rl"; open rl;
kernel.expname :=  "memof";
rl_train_only 8;

load "rl"; open rl;
kernel.expname := "seqprog";
rl_train_only 0;
rl_search_only 1;

load "rl"; open rl;
kernel.expname := "smartselect";
rl_search_cont_nowait ();

load "rl"; open rl;
kernel.expname := "smartselect";
train_smartselect 1;

*)
