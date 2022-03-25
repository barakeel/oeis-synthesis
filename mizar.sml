structure mizar :> mizar =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS 
  mlNeuralNetwork smlExecScripts mlTreeNeuralNetworkAlt dir

val ERR = mk_HOL_ERR "mizar"
fun eaddi x d = d := eadd x (!d)
fun ememi x d = emem x (!d)

type id = int
datatype sexp = Sexp of sexp list | Stoken of string;
datatype prog = Ins of (int * prog list);

fun prog_compare (Ins(s1,pl1),Ins(s2,pl2)) =
  cpl_compare Int.compare (list_compare prog_compare) ((s1,pl1),(s2,pl2))

fun prog_size (Ins(s,pl)) = case pl of
    [] => 1
  | [a] => 1 + prog_size a
  | [a,b] => 1 + prog_size a + prog_size b
  | _ => (length pl - 1) + sum_int (map prog_size pl) 

fun prog_to_clause p = (prog_size p, p)

fun prog_compare_size (p1,p2) = 
   cpl_compare Int.compare prog_compare (prog_to_clause p1, prog_to_clause p2)

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val simple_search = ref false
val simple_target = ref []

val use_mkl = ref false
val use_ob = ref false
val use_para = ref false
val dim_glob = ref 64
val ncore = 13 (* 20 *)
val ntarget = 13 * 6 * 4 (* 20 * 6 * 2 *)

(* -------------------------------------------------------------------------
   Conversions betwen lists of reals/ints and strings
   ------------------------------------------------------------------------- *)

fun string_to_real x = valOf (Real.fromString x)
fun ilts x = String.concatWith " " (map its x)
fun stil x = map string_to_int (String.tokens Char.isSpace x)
fun rlts x = String.concatWith " " (map rts x)
fun strl x = map string_to_real (String.tokens Char.isSpace x)

(* -------------------------------------------------------------------------
   Parsing S-expressions
   ------------------------------------------------------------------------- *)

fun lex_sexp_aux buf sl charl = case charl of
    [] => if null buf then rev sl else rev (implode (rev buf) :: sl)
  | #"(" :: m => 
   (
   if null buf 
   then lex_sexp_aux [] ("(" :: sl) m
   else lex_sexp_aux [] ("(" :: implode (rev buf) :: sl) m
   )
  | #")" :: m => 
   (
   if null buf 
   then lex_sexp_aux [] (")" :: sl) m
   else lex_sexp_aux [] (")" :: implode (rev buf) :: sl) m
   )
  | #" " :: m => 
   (
   if null buf 
   then lex_sexp_aux [] sl m
   else lex_sexp_aux [] (implode (rev buf) :: sl) m
   )
  | a :: m => lex_sexp_aux (a :: buf) sl m
  
fun lex_sexp s = lex_sexp_aux [] [] (explode s)
 
fun parse_sexpl sexpl sl = case sl of
    [] => (rev sexpl, [])
  | "(" :: m =>
    let val (a,contl) = parse_sexpl [] m in
      parse_sexpl (Sexp a :: sexpl) contl     
    end
  | ")" :: m => (rev sexpl, m)
  | a :: m => parse_sexpl (Stoken a :: sexpl) m 

fun parse_sexp s =
  let val (l1,l2) = parse_sexpl [] (lex_sexp s) in
    case (l1,l2) of
     ([a],[]) => a 
    | _ => raise ERR "parse_sexp" s
  end

fun rm_squote s = 
  if String.size s = 0 then s else
  if String.sub (s,0) = #"'" andalso 
     String.sub (s,String.size s - 1) =  #"'" 
  then String.substring (s,1,String.size s - 2)
  else s;

fun rm_squote_sexp sexp = case sexp of
    Sexp sexpl => Sexp (map rm_squote_sexp sexpl)
  | Stoken s => Stoken (rm_squote s);

fun collect_tokens sexp =  case sexp of
    Sexp sexpl => List.concat (map collect_tokens sexpl)
  | Stoken s => [s];

fun sexp_to_prog operd sexp = case sexp of 
    Sexp (Stoken s :: m) => Ins (dfind s operd, map (sexp_to_prog operd) m)
  | Stoken s => Ins (dfind s operd, [])
  | _ => raise ERR "sexp_to_prog" "not supported"


(* -------------------------------------------------------------------------
   Maximal arity is 3
   ------------------------------------------------------------------------- *) 

fun compress_arg_loop i s m =
  if length m <= 3 then m else 
  let
    val batchl = mk_batch_full 3 m
    fun f x = case x of
      [] => raise ERR "compress_arg_loop" ""
    | [a] => a
    | _ => 
      let val r = Sexp (Stoken (s ^ "@" ^ its (!i)) :: x) in
        incr i; r
      end 
  in
    compress_arg_loop i s (map f batchl)
  end

fun compress_arg s m =
  let val i = ref 0 in
    compress_arg_loop i s m
  end

fun compress_arity sexp = 
  case sexp of
    Sexp (Stoken s :: m) => 
    let val newm = map compress_arity m in
      Sexp (Stoken s :: compress_arg s newm)
    end
  | Stoken s => sexp
  | _ => raise ERR "compress_arity" "not supported"

(*
load "mizar"; open aiLib mizar;
parse_sexp "(1 (2 3))";
*)

fun prog_to_sexp revoperd (Ins (id,pl)) = case pl of 
    [] => Stoken (dfind id revoperd)
  | _ => Sexp (Stoken (dfind id revoperd) :: (map (prog_to_sexp revoperd) 
    pl))

val sexpl = map (compress_arity o rm_squote_sexp o parse_sexp) 
  (first_n 1000 (readl "data/00all_sorted.lisp_ar"));
val tokenl = List.concat (map collect_tokens sexpl);
val tokend = count_dict (dempty String.compare) tokenl;
val operd = dnew String.compare (number_snd 0 (dkeys tokend)); 
val revoperd = dnew Int.compare (map swap (dlist operd)); 
val progl = map (sexp_to_prog operd) sexpl;

fun string_of_sexp sexp = case sexp of
    Sexp l => "(" ^ String.concatWith " " (map string_of_sexp l) ^ ")"
  | Stoken s => s

fun collect_arity_one d (Ins (id,pl)) =
  (
  if dmem id (!d) 
  then 
    if length pl = dfind id (!d) 
    then () 
    else raise ERR "collect_arity" 
      (string_of_sexp (prog_to_sexp revoperd (Ins (id,pl))))
  else d := dadd id (length pl) (!d)
  ;
  app (collect_arity_one d) pl
  )

fun collect_arity pl =
  let val d = ref (dempty Int.compare) in
    app (collect_arity_one d) pl; !d
  end

val arityd = collect_arity progl;
val maxoper = dlength arityd
fun arity_of_oper opern = dfind opern arityd

(* -------------------------------------------------------------------------
   Test for a win
   ------------------------------------------------------------------------- *)

val mizard = enew prog_compare progl
val wind = ref (eempty prog_compare)
fun init_wind () = wind := eempty prog_compare
fun update_wind p = if emem p mizard then eaddi p wind else ()

(* -------------------------------------------------------------------------
   Parameters
   ------------------------------------------------------------------------- *)

val maxbigsteps = 1
val noise_flag = ref false
val noise_coeff_glob = ref 0.1
val nsim_opt = ref (NONE)
val time_opt = ref (SOME 60.0)
fun string_of_timeo () = (case !time_opt of
    NONE => "Option.NONE"
  | SOME s => "Option.SOME " ^ rts s)
fun spiky_noise () = if random_real () > 0.9 then 1.0 else 0.0
fun uniform_noise () = 1.0
val uniform_flag = ref false
fun random_noise () = random_real ()

fun mctsparam () =
  {explo_coeff = 1.0,
   noise = !noise_flag, noise_coeff = !noise_coeff_glob, 
   noise_gen = if !uniform_flag then uniform_noise else random_noise,
   nsim = !nsim_opt : int option, time = !time_opt: real option};

val coreid_glob = ref 0
val ngen_glob = ref 0


(* -------------------------------------------------------------------------
   Main process loging function
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

type tnn = mlTreeNeuralNetworkAlt.tnn
type 'a set = 'a Redblackset.set

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = int
val movel = List.tabulate (32,I)
fun string_of_move m = its m

(* -------------------------------------------------------------------------
   Build a list of programs
   ------------------------------------------------------------------------- *)

fun partopt_aux n acc l =
  if n <= 0 then SOME (rev acc,l)
  else if null l then NONE
  else partopt_aux (n - 1) (hd l :: acc) (tl l);

fun partopt n l = partopt_aux n [] l;

fun longereq n l =
  if n <= 0 then true else if null l then false else longereq (n-1) (tl l)

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = int list * prog list
type player = (board,move) psMCTS.player
fun string_of_board (board : board) = "board"
fun board_compare (a,b) = 
  cpl_compare (list_compare Int.compare) (list_compare prog_compare) (a,b)

(* -------------------------------------------------------------------------
   Application of a move to a board
   ------------------------------------------------------------------------- *)
fun eval_revil v il = case il of
    [] => raise ERR "eval_revil" ""
  | [a] => v * 16 + a
  | a :: m => eval_revil (v * 16 + a) m 
  
fun eval_il il = eval_revil 0 il

fun apply_moveo move (il,pl) = 
  if move >= 16 andalso int_pow 16 (length pl + 1) >= maxoper then NONE
  else if move >= 16 then SOME (move - 16 :: il, pl) 
  else if move = 0 andalso not (null il) then NONE else
  let  
    val opern = eval_il (move :: il) 
  in
    if opern >= maxoper then NONE else
    case partopt (arity_of_oper opern) pl of 
      NONE => NONE 
    | SOME (pla,plb) => 
       let val newp = Ins (opern, rev pla) in
         update_wind newp;
         SOME ([], newp :: plb)
       end
  end
 
fun apply_move move board = 
  valOf (apply_moveo move board)
  handle Option => raise ERR "apply_move" "option"

(* -------------------------------------------------------------------------
   Available moves
   ------------------------------------------------------------------------- *)

fun available_move board move = isSome (apply_moveo move board)
fun available_movel board = filter (available_move board) movel

(* -------------------------------------------------------------------------
   For debugging
   ------------------------------------------------------------------------- *)

fun random_step board =
  apply_move (random_elem (available_movel board)) board

fun random_board n = funpow n random_step ([],[])
  handle Interrupt => raise Interrupt 
    | _ => random_board n

fun random_prog n = last (snd (random_board n))

fun apply_movel movel board = foldl (uncurry apply_move) board movel

(* -------------------------------------------------------------------------
   Board status (all the checking/caching is done during apply move now)
   ------------------------------------------------------------------------- *)

fun status_of (board : board) = Undecided

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = status_of,
  available_movel = available_movel,
  apply_move = apply_move,
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = Int.compare,
  movel = movel
  }

fun player_uniform tnn board = 
  (0.0, map (fn x => (x,1.0)) (available_movel board))

fun mctsobj tnn = 
  {game = game, mctsparam = mctsparam (), player = player_uniform tnn};

fun tree_size tree = case tree of
    Leaf => 0
  | Node (node,ctreev) => 1 + 
     sum_int (map (tree_size o #3) (vector_to_list ctreev))

(*
nm1_hidden__1
removes foralls


load "mizar"; open mizar aiLib psMCTS;
dlength operd;
avoid_lose := true;
time_opt := SOME 60.0;
nsim_opt := NONE;
(* noise_flag := true;
  noise_coeff_glob := 0.9; *)
val mizarl = first_n 10 (dict_sort prog_compare_size (elist mizard));
map (string_of_sexp mizarl);
val _ = init_wind ();
val tnn = dempty Term.compare : mlTreeNeuralNetworkAlt.tnn;
val tree = starting_tree (mctsobj tnn) ([],[]);
PolyML.print_depth 1;
val (newtree,t) = add_time (mcts (mctsobj tnn)) tree;
PolyML.print_depth 40;
val n1 = tree_size newtree;
val n2 = elength (!wind);


map (string_of_sexp o (prog_to_sexp revoperd)) (elist (!wind));

map (string_of_sexp o (prog_to_sexp revoperd)) mizarl;

*)

(*

(* -------------------------------------------------------------------------
   Represent board as a term to give to the TNN
   ------------------------------------------------------------------------- *)

val alpha2 = rpt_fun_type 2 alpha
val alpha3 = rpt_fun_type 3 alpha

(* encoding sequences *)
val natbase = 16
fun embv_nat i = mk_var ("nat" ^ its i,alpha);
val natoperl = List.tabulate (natbase,embv_nat) @ [nat_cat,nat_neg,nat_big];

fun term_of_nat n =
  if n < 0 orelse n >= 16 
  then raise ERR "term_of_nat" ""
  else embv_nat n

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
val pair_cat = mk_var ("pair_cat",alpha3);
val stack_empty = mk_var ("stack_empty", alpha);
val stack_cat = mk_var ("stack_cat", alpha3);

fun term_of_stack_aux pl = case pl of 
    [] => stack_empty
  | a :: m => 
    cap (list_mk_comb (stack_cat, [term_of_prog a,term_of_stack_aux m]));

val pair_progseq = mk_var ("pair_progseq", alpha3);

fun term_of_stack (il,pl) =
  list_mk_comb (pair_progseq, [term_of_stack_aux pl, cap (term_of_seq il)])

(* policy head *)
val prepoli = mk_var ("prepoli",alpha2)
val head_poli = mk_var ("head_poli", alpha2)

fun term_of_board board = mk_comb (head_poli, 
  mk_comb (prepoli, term_of_stack board))

(* embedding dimensions *)
val operl = vector_to_list operv @ [stack_empty,stack_cat,pair_cat]
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

(* -------------------------------------------------------------------------
   Create the sequence of moves that would produce a program p
   ------------------------------------------------------------------------- *)

fun is_appsyn target prev move =
  case apply_moveo move prev of
    NONE => false
  | SOME (C1 clause :: m) => equal_prog (target,unzip_prog (snd clause))
  | _ => false

fun invapp_move board = case board of
    ([],[]) => NONE
  | ([], (Ins (id,argl) :: pl) => SOME ((mk_base16 id, rev argl @ pl),pl) 
  | (i :: il, pl) => SOME ((il,pl), i)

fun linearize_aux acc board = case invapp_move board of
    SOME (prev,move) => linearize_aux ((prev,move) :: acc) prev
  | NONE => acc

fun linearize p = linearize_aux [] ([],[p])

fun merge_sol pl =
  let
    val _ = log ("all solutions (past + concurrent): " ^ its (length pl))
    val pl0 = dict_sort prog_compare pl
    val _ = log ("uniques:" ^ its (length pl0))
  in
    pl0
  end

(* -------------------------------------------------------------------------
   Merge examples from different solutions
   ------------------------------------------------------------------------- *)

fun regroup_ex bml = 
  let fun f ((board,move),d) = 
    let 
      val oldv = dfind board d handle NotFound => 
        (Vector.tabulate (maxmove, fn _ => 0))
      val movei = index_of_move move
      val newv = Vector.update (oldv, movei, Vector.sub (oldv,movei) + 1)
    in
      dadd board newv d
    end
  in
    foldl f (dempty board_compare) bml
  end

fun pol_of_progl pold board = 
  normalize_proba (map Real.fromInt (vector_to_list (dfind board pold)))

fun create_ex pold (board,_) =
  (term_of_board board, pol_of_progl pold board)

fun create_exl progl =
  let 
    val bmll = map linearize prog
    val pold = regroup_ex (List.concat bmll)
  in
    map (create_ex pold) bmll
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
       ilts (l @ List.tabulate (4 - length l, fn _ => 99))
    fun pad_obj l = 
       if null l then empty_sobj else 
       rlts (l @ List.tabulate (!dim_glob - length l, fn _ => 9.0))
  in
    (
    String.concatWith " " (map (pad_sub o enc_sub) subtml),
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

fun fp_emb_either tnn oper newembl = 
  (* if !use_ob andalso !ngen_glob > 0 
  then (!fp_op_glob) oper newembl
  else *) fp_emb tnn oper newembl 
     
   
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
    val pol2 = map (fn x => (x, Vector.sub (pol1, index_of_move x))) amovel
  in
    (rewardf board, pol2)
  end

fun player_wtnn_cache tnn board =
  let
    (* val _ = if !debug_flag then print "." else () *)
    val _ = if dlength (!embd) > 1000000
            then embd := dempty Term.compare else ()
    val tm = term_of_stack board
    val (_,preboarde) = infer_emb_cache tnn tm
      handle NotFound => 
        raise ERR "player_wtnn_cache1" (string_of_board board)
    val prepolie = fp_emb_either tnn prepoli [preboarde]
    val pol1 = Vector.fromList (descale_out (fp_emb_either tnn head_poli 
      [prepolie]))
    val amovel = available_movel board
    val pol2 = map (fn x => (x, Vector.sub (pol1, index_of_move x))) amovel
  in
    (rewardf board, pol2)
  end

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val player_glob = ref player_wtnn_cache

fun mctsobj tnn = 
  {game = game, mctsparam = mctsparam (), player = !player_glob tnn};

fun tree_size tree = case tree of
    Leaf => 0
  | Node (node,ctreev) => 1 + 
     sum_int (map (tree_size o #3) (vector_to_list ctreev))

(* -------------------------------------------------------------------------
   Reinforcement learning loop utils
   ------------------------------------------------------------------------- *)

fun tnn_file ngen = selfdir ^ "/exp/" ^ !expname ^ "/tnn" ^ its ngen
fun sold_file ngen = selfdir ^ "/exp/" ^ !expname ^ "/sold" ^ its ngen

fun get_expdir () = selfdir ^ "/exp/" ^ !expname

fun mk_dirs () = 
  let val expdir = selfdir ^ "/exp/" ^ !expname in
    mkDir_err (selfdir ^ "/exp");
    mkDir_err expdir;
    mkDir_err (selfdir ^ "/parallel_search");
    expdir
  end

fun update_sold ((seq,prog),sold) =
  let 
    val oldprog = dfind seq sold
  in
    if prog_compare_size (prog,oldprog) = LESS 
    then dadd seq prog sold
    else sold
  end
  handle NotFound => dadd seq prog sold

fun write_sold ngen tmpname d = 
  (
  write_progl (sold_file ngen ^ tmpname) (elist d);
  write_progl (sold_file ngen) (elist d)
  )

fun read_sold ngen = enew prog_compare (read_progl (sold_file ngen))

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

fun read_ctnn_fixed () = 
  let val matl = read_ctnn (readl (selfdir ^ "/tnn_in_c/tnn")) in
    dnew Term.compare (combine (operlext,matl))
  end

fun trainf tmpname =
  let 
    val sold = read_sold (!ngen_glob) 
    val _ = print_endline ("reading sold " ^ (its (elength sold)))
    val seqpl = find_minirep_train (elist sold)
    val _ = print_endline (its (length seqpl) ^ " minimal representants")
    val ex = create_exl (shuffle seqpl)
    val _ = print_endline (its (length ex) ^ " examples created")
  in
    if !use_mkl then
      let
        val cfile = tnn_file (!ngen_glob) ^ tmpname ^ "_C"
        val sbin = if !use_para then "./tree_para" else "./tree"
        val _= 
          (
          print_endline "exporting training data";
          export_traindata ex;
          print_endline "exporting end";
          OS.Process.sleep (Time.fromReal 1.0);
          cmd_in_dir (selfdir ^ "/tnn_in_c") 
          (sbin ^ " > " ^ cfile)
          )
        val _ = OS.Process.sleep (Time.fromReal 1.0)
        (* val _ = if !use_ob then 
          cmd_in_dir (selfdir ^ "/tnn_in_c") ("sh compile_ob.sh")
          else () *)
        val matl = read_ctnn (readl cfile)
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
    ["open mcts;",
     "expname := " ^ mlquote (!expname) ^ ";",
     "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir) ^ ";",
     "mcts.ngen_glob := " ^ its (!ngen_glob) ^ ";",
     "mcts.dim_glob := " ^ its (!dim_glob) ^ ";",
     "mcts.use_mkl := " ^ bts (!use_mkl) ^ ";",
     "mcts.use_para := " ^ bts (!use_para) ^ ";",
     "mcts.use_ob := " ^ bts (!use_ob) ^ ";",
     "bloom.init_od ();",
     "trainf " ^ mlquote tmpname];
     exec_script scriptfile
  end

(* -------------------------------------------------------------------------
   Minimizing solutions using an initialized minid
   ------------------------------------------------------------------------- *)

fun minimize p =
  let 
    val sem = sem_of_prog p 
      handle Option => raise ERR "minimize" ""
    val (Ins (id,pl)) = (unzip_prog o snd o (dfind sem)) (!minid) 
      handle NotFound => p
  in
    Ins (id, map minimize pl)
  end

fun minimize_winl winl =
   let 
     val i = ref 0
     fun f p = 
       if not (is_executable p) then raise ERR "minimize_winl" (humanf p) else
       let val newp = commute (minimize p) in
         if equal_prog (p,newp) orelse depend_on_i newp then p
         else if same_sem newp p then (incr i; newp) else p
       end
     val r = map f winl
   in
     (r,!i)
   end

(* -------------------------------------------------------------------------
   Initialized dictionaries with previous solutions and their subterms
   ------------------------------------------------------------------------- *)

fun zerob b =
  let 
    val n = BoolArray.length b
    fun loop i = 
      if i >= n then () else 
      (BoolArray.update (b,i,false); loop (i+1))
  in
    loop 0
  end

val use_cache = ref false

fun init_dicts pl =
  let
    val _ = if not (!use_cache) then () else 
      let 
        fun test p = (check_simple_target p; NONE) 
          handle ResultP newp => SOME newp
        val plsol = List.mapPartial test pl 
      in
        if null plsol then () else 
        raise ResultP (hd (dict_sort prog_compare_size plsol))
      end
    val pil = map zip_prog pl
    val psemtiml = map_assoc (valOf o semtimo_of_prog) pl
      handle Option => raise ERR "init_dicts" ""  
    val seml = map (fst o snd) psemtiml
    fun g (p,(sem,tim)) = 
      (sem, (spacetime (prog_size p) tim, zip_prog p))
  in
    progd := eempty progi_compare;
    notprogd := eempty progi_compare;
    if !use_semb then 
       (semb := BoolArray.tabulate (bmod, fn _ => false);
        zerob (!semb)) 
    else semd := eempty seq_compare;
    embd := dempty Term.compare;
    seqwind := eempty seq_compare;
    progwind := eempty progi_compare;
    initd := enew progi_compare pil;
    minid := dnew seq_compare (map g psemtiml)
  end

(* -------------------------------------------------------------------------
   Main search function
   ------------------------------------------------------------------------- *)

val wnoise_flag = ref false

fun search tnn coreid =
  let
    val _ = print_endline "initialization"
    val _ = coreid_glob := coreid
    val _ = player_glob := player_wtnn_cache
    val sold = if !ngen_glob <= 0
               then eempty prog_compare
               else read_sold (!ngen_glob - 1)
    val _ = noise_flag := false
    val _ = if !coreid_glob mod 2 = 0 
            then (noise_flag := true; noise_coeff_glob := 0.1) else ()
    val (targetseq,seqnamel) = random_elem (dlist (!odname_glob))
    val _ = target_glob := targetseq
    val _ = print_endline 
      ("target: " ^ String.concatWith "-" seqnamel ^ ": " ^ 
        string_of_seq (!target_glob));
    val _ = init_dicts (elist sold)
    val _ = in_search := true
    val _ = avoid_lose := true
    val tree = starting_tree (mctsobj tnn) []
    val _ = print_endline "start search"
    val (newtree,t) = add_time (mcts (mctsobj tnn)) tree
    val _ = print_endline "end search"
    val n = tree_size newtree
    val _ = avoid_lose := false
    val _ = in_search := false
    val winl = map unzip_prog (elist (!progwind))
    val (minwinl,minn) = minimize_winl winl
    val _ = if emem (!target_glob) (!seqwind)
      then print_endline "target acquired"
      else print_endline "target missed"
  in
    print_endline ("search time: "  ^ rts_round 2 t ^ " seconds");
    print_endline ("tree_size: " ^ its n);
    print_endline ("prog sol: " ^ its (elength (!progwind)));
    print_endline ("prog mini: " ^ its minn);
    print_endline ("seq sol: " ^ its (elength (!seqwind)));
    minwinl
  end

val parspec : (tnn,int,prog list) extspec =
  {
  self_dir = selfdir,
  self = "mcts.parspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["bloom.init_od ()",
     "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "mcts.expname := " ^ mlquote (!expname),
     "mcts.ngen_glob := " ^ its (!ngen_glob),
     "mcts.coreid_glob := " ^ its (!coreid_glob),
     "mcts.dim_glob := " ^ its (!dim_glob),
     "mcts.time_opt := " ^ string_of_timeo (),
     "mcts.use_ob := " ^ bts (!use_ob)
   ] 
    ^ ")"),
  function = search,
  write_param = write_tnn,
  read_param = read_tnn,
  write_arg = let fun f file arg = writel file [its arg] in f end,
  read_arg = let fun f file = string_to_int (hd (readl file)) in f end,
  write_result = write_progl,
  read_result = read_progl
  }

fun search_target_aux (tnn,sold) tim target =
  let
    val _ = simple_search := true
    val _ = time_opt := SOME tim;
    val _ = player_glob := player_wtnn_cache
    val _ = simple_target := target
    val _ = target_glob := target
    val _ = init_dicts (elist sold)
    val _ = in_search := true
    val _ = avoid_lose := true
    val tree = starting_tree (mctsobj tnn) []
    val (newtree,t) = add_time (mcts (mctsobj tnn)) tree
    val _ = avoid_lose := false
    val _ = in_search := false
  in
    NONE
  end
  handle ResultP p => SOME (minimize p)

fun parsearch_target tim target =
  let 
    val tnn = read_tnn (selfdir ^ "/main_tnn")
    val sold = enew prog_compare (read_progl (selfdir ^ "/main_sold"))
    val (p,t) = add_time (search_target_aux (tnn,sold) tim) target 
  in
    (true,humanf (valOf p),t) handle Option => (false, "", t)
  end

val partargetspec : (real, seq, bool * string * real) extspec =
  {
  self_dir = selfdir,
  self = "mcts.partargetspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["bloom.init_od ()",
     "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir),
     "mcts.use_semb := " ^ bts (!use_semb),
     "mcts.use_ob := " ^ bts (!use_ob)
    ] 
    ^ ")"),
  function = parsearch_target,
  write_param = let fun f file param = writel file [rts param] in f end,
  read_param =  let fun f file = string_to_real (hd (readl file)) in f end,
  write_arg = let fun f file arg = writel file [ilts arg] in f end,
  read_arg = let fun f file = stil (hd (readl file)) in f end,
  write_result = let fun f file (b,s,t) = writel file [bts b, s, rts t] 
     in f end,
  read_result = let fun f file = 
       let val (s1,s2,s3) = triple_of_list (readl file) in 
         (string_to_bool s1, s2, string_to_real s3)
       end
     in f end
  }

fun parsearch_targetl ncore tim targetl =
  (
  buildheap_options := "--maxheap 10000";
  parmap_queue_extern ncore partargetspec tim targetl
  )

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun human_progseq p = 
  let 
    val seq = seq_of_prog p
    val seql = find_wins p seq
    val _ = if null seql 
      then log ("Error: human_progseq 1: " ^ (humanf p)) else ()
    fun f x = String.concatWith "-" (dfind x (!odname_glob)) ^ ": " ^ 
      String.concatWith " " (map its x)
  in
    humanf p ^ "\n" ^ String.concatWith "\n" (map f seql)
  end
  handle Interrupt => raise Interrupt | _ => 
    (log ("Error: human_progseq 2: " ^ (humanf p)); "")

fun human_progfreq (prog,freq) = its freq ^ ": " ^ humanf prog;

fun compute_freq f sol1 =
  let val freql = dlist 
    (count_dict (dempty prog_compare) (List.concat (map f sol1)))
  in
    dict_sort compare_imax freql
  end

fun stats_sol prefix sol =
  let
    val solsort = dict_sort prog_compare_size sol
    val freql1 = compute_freq all_subprog sol
    val freql2 = compute_freq under_lambda sol
  in
    polynorm_flag := false;
    writel (prefix ^ "prog") (map human_progseq solsort);
    writel (prefix ^ "freq") (map human_progfreq freql1);  
    writel (prefix ^ "freqlam") (map human_progfreq freql2);
    polynorm_flag := true;
    writel (prefix ^ "prog_poly") (map human_progseq solsort);
    writel (prefix ^ "freq_poly") (map human_progfreq freql1);
    writel (prefix ^ "freqlam_poly") (map human_progfreq freql2)
  end

fun stats_ngen dir ngen =
  let 
    val solprev = 
      if ngen = 0 then [] else #read_result parspec (sold_file (ngen - 1))
    val solnew = #read_result parspec (sold_file ngen)
    val prevd = enew prog_compare solprev
    val soldiff = filter (fn x => not (emem x prevd)) solnew
  in
    stats_sol (dir ^ "/full_") solnew;
    stats_sol (dir ^ "/diff_") soldiff
  end
  handle Interrupt => raise Interrupt | _ => log ("Error: stats_ngen")

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
    val _ = buildheap_options := "--maxheap 15000"
    val loop2_tm = Vector.sub (operv,13)
    val tnn = if ngen <= 0 
              then random_tnn (get_tnndim ())
              else read_tnn (tnn_file (ngen - 1))
    val sold = if ngen <= 0
               then eempty prog_compare
               else read_sold (ngen - 1)
    val (progll,t) = add_time
      (parmap_queue_extern ncore parspec tnn) 
         (List.tabulate (ntarget,I))
    val _ = log ("search time: " ^ rts_round 6 t)
    val _ = log ("solutions for each core:")
    val _ = log (String.concatWith " " (map (its o length) progll))
    val seqd = enew seq_compare (mapfilter seq_of_prog (elist sold))
    fun is_new p = not (emem (seq_of_prog p) seqd) 
      handle Interrupt => raise Interrupt | _ => false
    val newprogll = map (filter is_new) progll
    val _ = log ("new solutions for each core:")
    val _ = log (String.concatWith " " (map (its o length) newprogll))
    val progl = mk_fast_set prog_compare (
      List.concat progll @ elist sold)
    val newsold = enew prog_compare (merge_sol progl)
  in
    write_sold ngen tmpname newsold;
    stats_ngen (!buildheap_dir) ngen
  end

and rl_search tmpname ngen = 
  (rl_search_only tmpname ngen; rl_train tmpname ngen)

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

*)

end (* struct *)


(*
  -------------------------------------------------------------------------
  Train oeis-synthesis
  ------------------------------------------------------------------------- 

load "mcts"; open mcts;
expname := "run102";
time_opt := SOME 600.0;
use_mkl := true;
bloom.init_od ();
rl_search "_test11" 99;

(* testing *)
load "mcts"; open mcts; open aiLib; open kernel;
time_opt := SOME 60.0;
val tnn = mlTreeNeuralNetworkAlt.random_tnn (get_tnndim ());
bloom.init_od ();
use_semb := true;
val x = search tnn 0;
val sol1 = x;
(* val sol1 = random_subset 1000 (read_progl "main_sold"); *)
val ntot1 = sum_int (map prog_size sol1);
val freql0 = compute_freq all_subprog sol1;
fun distr_holes (a,i) = map (fn x => (x,i)) (all_holes a);
val freql1 = List.concat (map distr_holes freql0);
val freql11 = dict_sort compare_imax 
  (dlist (dsum prog_compare (freql0 @ freql1)));

(*
val freql2 = List.concat (map distr_holes freql11);
val freql22 = dict_sort compare_imax (dlist (dsum prog_compare freql2));
val freql31 = map fst freql11;
val freql32 = filter (fn x => prog_size x >= 2) freql31;
*)

fun compression (pat,id)
val freql4 = first_n 200 freql11;
val freql4p = dict_sort prog_compare_size freql4;
val freql4i = number_snd 101 (rev freql4p);
val sol2 = map (psubstl freql4i) sol1; 
val ntot2 = sum_int (map real_size sol2);


*)
