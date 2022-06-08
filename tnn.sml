structure tnn :> tnn =
struct

open HolKernel Abbrev boolLib aiLib smlParallel mcts
  mlNeuralNetwork mlTreeNeuralNetwork kernel human bloom game 

val ERR = mk_HOL_ERR "tnn"
type tnn = mlTreeNeuralNetwork.tnn
type player = (board,move) player

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val use_mkl = ref true
val dim_glob = ref 128
val embd = ref (dempty Term.compare)

(* -------------------------------------------------------------------------
   I/O utils
   ------------------------------------------------------------------------- *)

fun string_to_real x = valOf (Real.fromString x)
fun ilts x = String.concatWith " " (map its x)
fun stil x = map string_to_int (String.tokens Char.isSpace x)
fun rlts x = String.concatWith " " (map rts x)
fun strl x = map string_to_real (String.tokens Char.isSpace x)

(* -------------------------------------------------------------------------
   Convert board into a tree (HOL4 term)
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

(* two layers *)
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
      if dlength (!embd) > 10000 then embd := dempty Term.compare else ();
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
  (0.0, map (fn x => (x,1.0)) (#available_movel game board))

fun player_wtnn tnn board =
  let 
    val rl = infer_tnn tnn [term_of_board board]
    val pol1 = Vector.fromList (snd (singleton_of_list rl))
    val amovel = #available_movel game board 
    val pol2 = map (fn x => (x, Vector.sub (pol1,x))) amovel
  in
    (rewardf board, pol2)
  end

fun player_wtnn_cache tnn board =
  let
    (* val _ = if !debug_flag then print "." else () *)
    val _ = if dlength (!embd) > 1000000
            then embd := dempty Term.compare else ()
    val tm = term_of_join board
    val (_,preboarde) = (infer_emb_cache tnn) tm
      handle NotFound => 
        raise ERR "player_wtnn_cache1" (#string_of_board game board)
    val prepolie = fp_emb_either tnn prepoli [preboarde]
    val ende = fp_emb_either tnn head_poli [prepolie]
    val pol1 = Vector.fromList (descale_out ende)
    val amovel = #available_movel game board
    val pol2 = map (fn x => (x, Vector.sub (pol1,x))) amovel
  in
    (rewardf board, pol2)
  end

val player_glob = ref player_wtnn_cache


(* -------------------------------------------------------------------------
   Create examples
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
   Export examples to MKL 
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
   Reading TNN produced by MKL training
   ------------------------------------------------------------------------- *)

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

fun read_ctnn_aux sl = case sl of
    [] => raise ERR "read_ctnn" ""
  | "START MATRICES" :: m => read_cmatl m
  | a :: m => read_ctnn_aux m

fun read_ctnn sl = dnew Term.compare (combine (operlext,read_ctnn_aux sl)) 

end (* struct *)

