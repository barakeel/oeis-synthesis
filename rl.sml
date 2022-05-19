structure rl :> rl =
struct

open HolKernel Abbrev boolLib aiLib smlParallel mcts
  mlNeuralNetwork smlExecScripts mlTreeNeuralNetwork kernel bloom execarb
  human

val ERR = mk_HOL_ERR "rl"

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val use_mkl = ref true
val dim_glob = ref 64
val ncore = ref 16
val ntarget = ref 160
val maxgen = ref NONE
val target_glob = ref []
val noise_flag = ref false
val noise_coeff_glob = ref 0.1
val nsim_opt = ref NONE
val time_opt = ref (SOME 600.0)

(* experiments *)
val randsol_flag = false
val randmin_flag = false

(* online search *)
val online_flag = ref false
exception ResultP of prog

(* -------------------------------------------------------------------------
   Utils
   ------------------------------------------------------------------------- *)

fun string_to_real x = valOf (Real.fromString x)
fun ilts x = String.concatWith " " (map its x)
fun stil x = map string_to_int (String.tokens Char.isSpace x)
fun rlts x = String.concatWith " " (map rts x)
fun strl x = map string_to_real (String.tokens Char.isSpace x)

fun butlast_string s = 
  if String.size s = 0 
  then raise ERR "butlast_string" "" 
  else String.substring (s,0,String.size s-1);

fun string_of_seq seq = 
  String.concatWith " " (map (butlast_string o Arbint.toString) seq)

(* -------------------------------------------------------------------------
   Dictionaries shortcuts
   ------------------------------------------------------------------------- *)

fun eaddi x d = d := eadd x (!d)
fun ememi x d = emem x (!d)
fun daddi k v d = d := dadd k v (!d) 
fun dmemi x d = dmem x (!d)

(* -------------------------------------------------------------------------
   Parameters
   ------------------------------------------------------------------------- *)

fun string_of_timeo () = (case !time_opt of
    NONE => "Option.NONE"
  | SOME s => "Option.SOME " ^ rts s)

fun spiky_noise () = if random_real () > 0.9 then 1.0 else 0.0
fun uniform_noise () = 1.0
fun random_noise () = random_real ()

fun mctsparam () =
  {explo_coeff = 1.0,
   noise = !noise_flag, noise_coeff = !noise_coeff_glob, 
   noise_gen = random_noise,
   nsim = !nsim_opt : int option, time = !time_opt: real option};

val coreid_glob = ref 0
val ngen_glob = ref 0
val in_search = ref false

val embd = ref (dempty Term.compare)
val wind = ref (dempty Int.compare)
val progd = ref (eempty prog_compare)

(* -------------------------------------------------------------------------
   Main process logging function
   ------------------------------------------------------------------------- *)

val expname = ref "test"

fun log s =
  let val expdir = selfdir ^ "/exp/" ^ !expname in
    print_endline s;
    append_endline (expdir ^ "/log") s
  end

(* -------------------------------------------------------------------------
   Type abbreviations
   ------------------------------------------------------------------------- *)

type seq = kernel.seq
type prog = kernel.prog
type tnn = mlTreeNeuralNetwork.tnn
type 'a set = 'a Redblackset.set
type ('a,'b) dict = ('a,'b) Redblackmap.dict

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = int
val movelg = List.tabulate (Vector.length operv, I)
val maxmove = length movelg
val maxarity = list_imax (vector_to_list (Vector.map arity_of operv))
val move_compare = Int.compare
fun string_of_move x = its x

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = prog list
type player = (board,move) mcts.player
 
fun string_of_board (board : board) = 
  String.concatWith " | " (map humanf board)

fun board_compare (a,b) = list_compare prog_compare (a,b)

(* -------------------------------------------------------------------------
   Check if a program is a solution (i.e) covers an OEIS sequence
   ------------------------------------------------------------------------- *)

fun update_wind_one d (anum,p) =
  case (SOME (dfind anum (!d)) handle NotFound => NONE) of 
    NONE => d := dadd anum p (!d)
  | SOME oldp =>
    if prog_compare_size (p,oldp) = LESS
    then d := dadd anum p (!d)
    else ()

fun update_wind_glob p =
  let
    val anuml = find_wins p
    fun f anum = update_wind_one wind (anum,p)  
  in
    app f anuml
  end

fun merge_isol isol = 
  let val d = ref (dempty Int.compare) in
    app (update_wind_one d) isol;
    dlist (!d)
  end

(* -------------------------------------------------------------------------
   Application of a move to a board
   ------------------------------------------------------------------------- *)

fun exec_fun p plb =
  (
  if !online_flag andalso not (depend_on_y p) andalso 
     not (ememi p progd)
    then (eaddi p progd; 
          if pcover p (!target_glob) then raise ResultP p else ())   
  else if !in_search andalso not (depend_on_y p)
     then eaddi p progd 
  else (); 
  SOME (p :: plb)
  )

fun apply_moveo move board =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 <> arity 
    then NONE 
    else exec_fun (Ins (move, rev l1)) l2 
  end

fun apply_move move board = valOf (apply_moveo move board)

(* -------------------------------------------------------------------------
   Available moves
   ------------------------------------------------------------------------- *)

fun available_movel board =
  filter (fn move => isSome (apply_moveo move board)) movelg

(* -------------------------------------------------------------------------
   For debugging
   ------------------------------------------------------------------------- *)

fun random_step board =
  apply_move (random_elem (available_movel board)) board

fun random_board n = funpow n random_step []
  handle Interrupt => raise Interrupt 
    | _ => random_board n

fun random_prog n = last (random_board n)
fun apply_movel movel board = foldl (uncurry apply_move) board movel

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  available_movel = available_movel,
  apply_move = apply_move,
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = move_compare,
  movel = movelg
  }

(* -------------------------------------------------------------------------
   Represent board as a term to give to the TNN
   ------------------------------------------------------------------------- *)

val alpha2 = rpt_fun_type 2 alpha
val alpha3 = rpt_fun_type 3 alpha

(* encoding sequences *)
val natbase = 10
val nat_cat = mk_var ("nat_cat", alpha3);
val nat_neg = mk_var ("nat_neg", alpha2);
val nat_big = mk_var ("nat_big", alpha);
fun embv_nat i = mk_var ("nat" ^ its i,alpha);
val natoperl = List.tabulate (natbase,embv_nat) @ [nat_cat,nat_neg,nat_big];

fun term_of_nat_aux n =
  if n < natbase then embv_nat n
  else list_mk_comb (nat_cat,
    [embv_nat (n mod natbase), term_of_nat_aux (n div natbase)])

local open Arbint in

fun term_of_nat n =
  if n < zero then mk_comb (nat_neg, term_of_nat (~ n))
  else if n > fromInt 1000000 then nat_big
  else term_of_nat_aux (toInt n)

end

val seq_empty = mk_var ("seq_empty", alpha);
val seq_cat = mk_var ("seq_cat", alpha3);

fun term_of_seq seq = case seq of
    [] => seq_empty
  | a :: m => list_mk_comb 
    (seq_cat, [term_of_nat a, term_of_seq m]);

val seqoperl = natoperl @ [seq_empty,seq_cat]

(* faking two layers *)
fun cap_tm tm = 
  let val name = fst (dest_var tm) in
    mk_var ("cap_" ^ name,alpha2)
  end

fun is_capped tm = 
  let val name = fst (dest_var (fst (strip_comb tm))) in
    String.isPrefix "cap_" name
  end

fun cap_opt tm = 
  if arity_of tm <= 0 
  then NONE
  else SOME (cap_tm tm)

fun cap tm = 
  let val oper = fst (strip_comb tm) in
    mk_comb (cap_tm oper, tm)
  end

(* syntactic *)
fun term_of_prog (Ins (id,pl)) = 
  if null pl then Vector.sub (operv,id) else
  cap (list_mk_comb (Vector.sub (operv,id), map term_of_prog pl))

(* stack *)
val stack_empty = mk_var ("stack_empty", alpha);
val stack_cat = mk_var ("stack_cat", alpha3);

fun term_of_stack stack = case stack of 
    [] => stack_empty
  | [a] => term_of_prog a
  | a :: m => 
    cap (list_mk_comb (stack_cat, [term_of_prog a, term_of_stack m]))

val pair_progseq = mk_var ("pair_progseq", alpha3);

fun term_of_join board = 
  list_mk_comb (pair_progseq, 
    [term_of_stack board, cap (term_of_seq (first_n 16 (!target_glob)))])

(* policy head *)
val prepoli = mk_var ("prepoli",alpha2)
val head_poli = mk_var ("head_poli", alpha2)

fun term_of_board board = mk_comb (head_poli, 
  mk_comb (prepoli, term_of_join board))

(* embedding dimensions *)
val operl = vector_to_list operv @ [stack_empty,stack_cat]
val operlcap = operl @ List.mapPartial cap_opt operl
val seqoperlcap = seqoperl @ [cap_tm seq_cat, cap_tm seq_empty]
val allcap = [pair_progseq] @ operlcap @ seqoperlcap

val operlext = allcap @ [prepoli,head_poli]
val opernd = dnew Term.compare (number_snd 0 operlext)

fun dim_std_alt oper =
  if arity_of oper = 0 
  then [0,!dim_glob] 
  else [!dim_glob * arity_of oper, !dim_glob]

fun get_tnndim () = 
  map_assoc dim_std_alt allcap @ 
    [(prepoli,[!dim_glob,!dim_glob]),(head_poli,[!dim_glob,maxmove])] 

(* -------------------------------------------------------------------------
   Create the sequence of moves that would produce a program p
   ------------------------------------------------------------------------- *)

fun invapp_move board = case board of
    [] => NONE
  | Ins (id,argl) :: m => SOME (rev argl @ m, id)

fun linearize_aux acc board = case invapp_move board of
    SOME (prev,move) => linearize_aux ((prev,move) :: acc) prev
  | NONE => acc

fun linearize p = linearize_aux [] [p]

fun linearize_safe p = 
  let 
    val l = linearize p
    val movel = map snd l
    val q = singleton_of_list (apply_movel movel [])
  in
    if prog_compare (p,q) = EQUAL then l else
    raise ERR "linearize" (humanf p ^ " different from " ^ humanf q)
  end

(* -------------------------------------------------------------------------
   Merge examples from different solutions
   ------------------------------------------------------------------------- *)

fun create_exl iprogl =
  let 
    val zerov = Vector.tabulate (maxmove, fn _ => 0.0)
    fun create_ex (i,p) = 
      let
        val _ = target_glob := valOf (Array.sub (oseq,i))
        val bml = linearize_safe p
        fun g (board,move) =
           let 
             val newv = Vector.update (zerov, move, 1.0)
             val newl = vector_to_list newv
           in
             (term_of_board board, newl)
           end
      in
        map g bml    
      end
  in
    map create_ex iprogl
  end

(* -------------------------------------------------------------------------
   Export examples to C
   ------------------------------------------------------------------------- *)

fun order_subtm tml =
  let
    val d = ref (dempty (cpl_compare Int.compare Term.compare))
    fun traverse tm =
      let
        val (oper,argl) = strip_comb tm
        val nl = map traverse argl
        val n = 1 + sum_int nl
      in
        d := dadd (n, tm) () (!d); n
      end
    val subtml = (app (ignore o traverse) tml; dkeys (!d))
  in
    map snd subtml
  end;

val empty_sobj = rlts (List.tabulate (!dim_glob, fn _ => 9.0))

fun linearize_ex tmobjl =
  let
    val objd = dnew Term.compare tmobjl
    val subtml = order_subtm (map fst tmobjl);
    val indexd = dnew Term.compare (number_snd 0 subtml);
    fun enc_sub x = 
      let val (oper,argl) = strip_comb x in
        dfind oper opernd :: map (fn x => dfind x indexd) argl
      end
    fun enc_obj x = dfind x objd handle NotFound => []
    fun pad_sub l = 
       ilts (l @ List.tabulate ((maxarity + 1) - length l, fn _ => 99))
    fun pad_obj l = 
       if null l then empty_sobj else 
       rlts (l @ List.tabulate (!dim_glob - length l, fn _ => 9.0))
  in
    (String.concatWith " " (map (pad_sub o enc_sub) subtml),
     String.concatWith " " (map (pad_obj o enc_obj) subtml),
     length subtml
    )
  end;

fun export_traindata ex =
  let
    val datadir = selfdir ^ "/tnn_in_c/data"
    val _ =
      (
      erase_file (datadir ^ "/arg.txt");
      erase_file (datadir ^ "/dag.txt");
      erase_file (datadir ^ "/obj.txt");
      erase_file (datadir ^ "/size.txt");
      erase_file (datadir ^ "/arity.txt");
      erase_file (datadir ^ "/head.txt")
      )
    val noper = length operlext
    val tmobjll = ex
    val nex = length tmobjll
    val (dagl,objl,sizel) = split_triple (map linearize_ex tmobjll);
    fun find_head tm = if term_eq tm head_poli then maxmove else 0
  in
    writel (datadir ^ "/arg.txt") (map its [noper,nex,!dim_glob]);
    writel (datadir ^ "/dag.txt") dagl;
    writel (datadir ^ "/obj.txt") objl;
    writel (datadir ^ "/size.txt") (map its sizel);
    writel (datadir ^ "/arity.txt") (map (its o arity_of) operlext);
    writel (datadir ^ "/head.txt") (map (its o find_head) operlext)
  end

(* -------------------------------------------------------------------------
   TNN cache
   ------------------------------------------------------------------------- *)

fun fp_emb_either tnn oper newembl = fp_emb tnn oper newembl
   
fun infer_emb_cache tnn tm =
  if is_capped tm 
  then 
    (
    Redblackmap.findKey (!embd,tm) handle NotFound =>
    let
      val (oper,argl) = strip_comb tm
      val embl = map (infer_emb_cache tnn) argl
      val (newargl,newembl) = split embl
      val emb = fp_emb_either tnn oper newembl
      val newtm = list_mk_comb (oper,newargl)
    in
      embd := dadd newtm emb (!embd); 
      (newtm,emb)
    end
    )
  else
    let
      val (oper,argl) = strip_comb tm
      val embl = map (infer_emb_cache tnn) argl
      val (newargl,newembl) = split embl
      val emb = fp_emb_either tnn oper newembl
    in
      (tm,emb)
    end

(* -------------------------------------------------------------------------
   Players
   ------------------------------------------------------------------------- *)

fun rewardf board = 0.0

fun player_uniform tnn board = 
  (0.0, map (fn x => (x,1.0)) (available_movel board))

fun player_wtnn tnn board =
  let 
    val rl = infer_tnn tnn [term_of_board board]
    val pol1 = Vector.fromList (snd (singleton_of_list rl))
    val amovel = available_movel board 
    val pol2 = map (fn x => (x, Vector.sub (pol1,x))) amovel
  in
    (rewardf board, pol2)
  end

fun player_wtnn_cache_aux tnn board =
  let
    (* val _ = if !debug_flag then print "." else () *)
    val _ = if dlength (!embd) > 1000000
            then embd := dempty Term.compare else ()
    val tm = term_of_join board
    val (_,preboarde) = (infer_emb_cache tnn) tm
      handle NotFound => 
        raise ERR "player_wtnn_cache1" (string_of_board board)
    val prepolie = fp_emb_either tnn prepoli [preboarde]
    val ende = fp_emb_either tnn head_poli [prepolie]
    val pol1 = Vector.fromList (descale_out ende)
    val amovel = Profile.profile "available_movel" available_movel board
    val pol2 = map (fn x => (x, Vector.sub (pol1,x))) amovel
  in
    (rewardf board, pol2)
  end

fun player_wtnn_cache tnn board = 
  Profile.profile "player_wtnn_cache"
  (player_wtnn_cache_aux tnn) board

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val player_glob = ref player_wtnn_cache

fun mctsobj tnn = 
  {game = game, mctsparam = mctsparam (), player = !player_glob tnn};

(* -------------------------------------------------------------------------
   Reinforcement learning loop utils
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

fun write_isol ngen tmpname iprogl = 
  (
  write_iprogl (isol_file ngen ^ tmpname) iprogl;
  write_iprogl (isol_file ngen) iprogl
  )
fun read_isol ngen = read_iprogl (isol_file ngen)


(* -------------------------------------------------------------------------
   training
   ------------------------------------------------------------------------- *)

val ncoretrain = 4

val schedule =
  [
   {ncore = ncoretrain, verbose = true, learning_rate = 0.03,
    batch_size = 16, nepoch = 40},
   {ncore = ncoretrain, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 10},
   {ncore = ncoretrain, verbose = true, learning_rate = 0.01,
    batch_size = 16, nepoch = 10},
   {ncore = ncoretrain, verbose = true, learning_rate = 0.007,
    batch_size = 16, nepoch = 10},
   {ncore = ncoretrain, verbose = true, learning_rate = 0.005,
    batch_size = 16, nepoch = 10}
  ];

fun read_mat acc sl = case sl of
    [] => (rev acc, [])
  | "A" :: m => (rev acc, sl)
  | x :: m => 
    let 
      val line1 = strl x
      val line2 = last line1 :: butlast line1 
      val line = Vector.fromList line2
    in
      read_mat (line :: acc) m
    end

fun read_cmatl sl = case sl of 
    [] => []
  | "A" :: m => 
    let 
      val (mat1,cont) = read_mat [] m
      val w1 = Vector.fromList mat1 
    in 
      (
      if Vector.length (Vector.sub (w1,0)) = 1
      then 
        [{a = mlNeuralNetwork.idactiv, 
          da = mlNeuralNetwork.didactiv,
          w = w1}]
      else 
        [{a = mlNeuralNetwork.tanh, 
          da = mlNeuralNetwork.dtanh,
          w = w1}]
      )
      :: read_cmatl cont
    end
  | x :: m => raise ERR "read_cmatl" x

fun read_ctnn sl = case sl of
    [] => raise ERR "read_ctnn" ""
  | "START MATRICES" :: m => read_cmatl m
  | a :: m => read_ctnn m

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
        val matl = read_ctnn (readl tnnsml_file)
        val tnn = dnew Term.compare (combine (operlext,matl))
      in
        write_tnn (tnn_file (!ngen_glob) ^ tmpname) tnn;
        write_tnn (tnn_file (!ngen_glob)) tnn
      end
    else
    let
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
     "expname := " ^ mlquote (!expname) ^ ";",
     "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir) ^ ";",
     "rl.ngen_glob := " ^ its (!ngen_glob) ^ ";",
     "rl.dim_glob := " ^ its (!dim_glob) ^ ";",
     "rl.use_mkl := " ^ bts (!use_mkl) ^ ";",
     "trainf " ^ mlquote tmpname];
     exec_script scriptfile
  end

(* -------------------------------------------------------------------------
   Initialized dictionaries with previous solutions and their subterms
   ------------------------------------------------------------------------- *)

fun init_dicts () =
  (
  progd := eempty prog_compare;
  embd := dempty Term.compare;
  wind := dempty Int.compare
  )

(* -------------------------------------------------------------------------
   Main search function
   ------------------------------------------------------------------------- *)

val wnoise_flag = ref false

fun search tnn coreid =
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
    val _ = init_dicts ()
    val _ = in_search := true
    val tree = starting_tree (mctsobj tnn) []
    val _ = print_endline "start search"
    val (newtree,t) = add_time (mcts (mctsobj tnn)) tree
    val _ = print_endline "end search"
    val n = tree_size newtree
    val _ = in_search := false
    val (_,t2) = add_time (app update_wind_glob) (elist (!progd))
    val _ = print_endline ("win check: "  ^ rts_round 2 t2 ^ " seconds")
    val r = dlist (!wind)
  in
    print_endline ("search time: "  ^ rts_round 2 t ^ " seconds");
    print_endline ("tree_size: " ^ its n);
    print_endline ("progd: " ^ its (elength (!progd)));
    print_endline ("solutions: " ^ its (dlength (!wind)));
    init_dicts ();
    PolyML.fullGC ();
    r
  end



val parspec : (tnn, int, (int * prog) list) extspec =
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
     "rl.dim_glob := " ^ its (!dim_glob),
     "rl.time_opt := " ^ string_of_timeo ()] 
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
   For interactive calls
   ------------------------------------------------------------------------- *)

fun search_target tnn target =
  let
    val _ = player_glob := player_wtnn_cache
    val _ = noise_flag := true
    val _ = target_glob := target
    val _ = init_dicts ()
    val _ = online_flag := true
    val tree = starting_tree (mctsobj tnn) []
    val (newtree,t) = add_time (mcts (mctsobj tnn)) tree
  in
    online_flag := false; init_dicts (); NONE
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
    val isolsort = dict_sort (snd_compare prog_compare) isol
    val freql1 = compute_freq all_subprog (map snd isol)
  in
    writel (prefix ^ "prog") (map string_of_iprog isolsort);
    writel (prefix ^ "freq") (map human_progfreq freql1)
  end

fun stats_ngen dir ngen =
  let 
    val solprev = 
      if ngen = 0 then [] else #read_result parspec (isol_file (ngen - 1))
    val solnew = #read_result parspec (isol_file ngen)
    val prevd = dnew Int.compare solprev
    val soldiff = filter (fn (i,_) => not (dmem i prevd)) solnew
  in
    stats_sol (dir ^ "/full_") solnew;
    stats_sol (dir ^ "/diff_") soldiff
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
    val isol = if ngen <= 0
               then []
               else read_isol (ngen - 1)
    val (iprogll,t) = add_time
      (parmap_queue_extern (!ncore) parspec tnn) (List.tabulate (!ntarget,I))
    val _ = log ("search time: " ^ rts_round 6 t)
    val _ = log ("solutions for each search:")
    val _ = log (String.concatWith " " (map (its o length) iprogll))
    val newisol = merge_isol (List.concat (isol :: iprogll))
  in
    write_isol ngen tmpname newisol;
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
  -------------------------------------------------------------------------
  Train oeis-synthesis
  ------------------------------------------------------------------------- 

load "rl"; open rl;
expname := "your_experiment";
rl_search "_main" 1;


*)
