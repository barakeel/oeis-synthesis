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

(* continous training/searching *)
val cont_flag = ref false
val startgen_cont = 100

(* -------------------------------------------------------------------------
   Logging function
   ------------------------------------------------------------------------- *)

fun log s = 
  (
  print_endline s;
  append_endline (selfdir ^ "/exp/" ^ !expname ^ "/log") s
  )

(* -------------------------------------------------------------------------
   Files
   ------------------------------------------------------------------------- *)

fun tnn_file ngen = selfdir ^ "/exp/" ^ !expname ^ "/tnn" ^ its ngen
fun isol_file ngen = selfdir ^ "/exp/" ^ !expname ^ "/isol" ^ its ngen

fun get_expdir () = selfdir ^ "/exp/" ^ !expname

fun mk_dirs () = 
  let val expdir = selfdir ^ "/exp/" ^ !expname in
    mkDir_err (selfdir ^ "/exp");
    mkDir_err expdir;
    mkDir_err (selfdir ^ "/parallel_search");
    expdir
  end

fun write_isol_atomic ngen tmpname iprogl = 
  let 
    val savefile = isol_file ngen ^ tmpname
    val newfile = isol_file ngen
    val oldfile = isol_file ngen ^ "_temp"
  in
    write_iprogl savefile iprogl;
    write_iprogl oldfile iprogl;
    OS.FileSys.rename {old = oldfile, new = newfile}
  end
  
fun read_isol ngen = read_iprogl (isol_file ngen)

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun find_isol ngen =
  if exists_file (isol_file ngen)
  then find_isol (ngen+1) 
  else 
    if exists_file (isol_file (ngen - 1))
    then read_iprogl (isol_file (ngen - 1))
    else raise ERR "find_isol" (its ngen)


fun write_tnn_atomic ngen tmpname tnn =
  let 
    val savefile = tnn_file ngen ^ tmpname
    val newfile = tnn_file ngen
    val oldfile = tnn_file ngen ^ "_temp"
  in
    write_tnn savefile tnn;
    write_tnn oldfile tnn;
    OS.FileSys.rename {old = oldfile, new = newfile}
  end

fun trainf tmpname =
  let 
    val isol = 
      if !cont_flag 
      then find_isol startgen_cont
      else read_isol (!ngen_glob) 
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
        write_tnn_atomic (!ngen_glob) tmpname tnn
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
      write_tnn_atomic (!ngen_glob) tmpname tnn
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
     "rl.cont_flag := " ^ bts (!cont_flag) ^ ";",
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
     "game.time_opt := " ^ string_of_timeo ()] 
    ^ ")"),
  function = search,
  write_param = write_tnn,
  read_param = read_tnn,
  write_arg = let fun f file arg = writel file [its arg] in f end,
  read_arg = let fun f file = string_to_int (hd (readl file)) in f end,
  write_result = write_iprogl,
  read_result = read_iprogl 
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

fun find_tnn ngen =
  if exists_file (tnn_file ngen)
  then find_tnn (ngen+1) 
  else 
    if exists_file (tnn_file (ngen - 1))
    then read_tnn (tnn_file (ngen - 1))
    else raise ERR "find_tnn" (its ngen)

fun rl_search_only tmpname ngen =
  let 
    val expdir = mk_dirs ()
    val _ = log ("Search " ^ its ngen)
    val _ = buildheap_dir := expdir ^ "/search" ^ its ngen ^ tmpname;
    val _ = mkDir_err (!buildheap_dir)
    val _ = ngen_glob := ngen
    val _ = buildheap_options := "--maxheap 8000"
    val tnn = if ngen <= 0 
              then random_tnn (get_tnndim ())
              else 
                if !cont_flag 
                then find_tnn startgen_cont
                else read_tnn (tnn_file (ngen - 1))
    val (isoll,t) = add_time
      (parmap_queue_extern (!ncore) parspec tnn) (List.tabulate (!ntarget,I))
    val _ = log ("search time: " ^ rts_round 6 t)
    val _ = log ("average number of solutions per search: " ^
                  rts_round 2 (average_int (map length isoll)))
    val oldisol = if ngen <= 0
                  then []
                  else read_isol (ngen - 1)
    val newisol = merge_isol (List.concat (oldisol :: isoll))
    val _ = log ("solutions: " ^ (its (length newisol)))
    val _ = count_newsol oldisol isoll
    val _ = write_isol_atomic ngen tmpname newisol
  in
    stats_ngen (!buildheap_dir) ngen
  end

fun rl_train_only tmpname ngen =
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



fun rl_search tmpname ngen = 
  (
  cont_flag := false;
  rl_search_only tmpname ngen; 
  if isSome (!maxgen) andalso ngen >= valOf (!maxgen) then () else 
  rl_train tmpname ngen
  )

and rl_train tmpname ngen = 
  (
  cont_flag := false; 
  rl_train_only tmpname ngen; 
  rl_search tmpname (ngen + 1)
  )


fun rl_search_cont tmpname ngen = 
  (
  cont_flag := true;
  rl_search_only tmpname ngen; 
  rl_search_cont tmpname (ngen + 1)
  )

fun rl_train_cont tmpname ngen = 
  (
  cont_flag := true; 
  rl_train_only tmpname ngen; 
  rl_train_cont tmpname (ngen + 1)
  )

(*
(* -------------------------------------------------------------------------
   OpenBlas Foreign Function Interface
   Be aware that using it (use_ob := true + installing openblas) 
   creates a difficult to reproduce bug.
   It seems that updating the binary during the search creates
   a bad file descriptor
   ------------------------------------------------------------------------- *)

fun fp_op_default oper embl = Vector.fromList [100.0]
val fp_op_glob = ref fp_op_default
val biais = Vector.fromList ([1.0])

local open Foreign in

fun update_fp_op () =
  let
    val lib = loadLibrary (selfdir ^ "/tnn_in_c/ob.so");
    val fp_op_sym = getSymbol lib "fp_op";
    val cra = cArrayPointer cDouble;
    val fp_op0 = buildCall3 (fp_op_sym,(cLong,cra,cra),cVoid);
    fun fp_op oper embl =
      let 
        val n = dfind oper opernd 
        val Xv = Vector.concat (embl @ [biais])
        val X = Array.tabulate (Vector.length Xv, fn i => Vector.sub (Xv,i))
        val Y = Array.tabulate (!dim_glob,fn i => 0.0)
      in 
        fp_op0 (n,X,Y);
        Array.vector Y
      end
  in
    fp_op_glob := fp_op
  end

end (* local *)



fun fp_emb_either tnn oper newembl = 
  (* if !use_ob andalso !ngen_glob > 0 
  then (!fp_op_glob) oper newembl
  else *) fp_emb tnn oper newembl 


  (* val _ = if !use_ob then 
    cmd_in_dir (selfdir ^ "/tnn_in_c") ("sh compile_ob.sh")
    else () *)
*)

end (* struct *)

(*
(* train/search loop *)
load "rl"; open rl;
expname := "run400";
rl_train "_m30" 100;

(* continous searching *)
load "rl"; open rl;
expname := "run400";
rl_search_cont "_m31" 101;

(* continuous training *)
load "rl"; open rl;
expname := "run400";
rl_train_cont "_m31" 101;

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
