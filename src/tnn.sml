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

val use_ob = ref true
val dim_glob = ref  
  (string_to_int (dfind "dim_glob" configd) handle NotFound => 96)
val embd = ref (dempty Term.compare)
  
val use_cache = ref false (* only used during export *)
val progtmd = ref (dempty prog_compare)
val seqtmd = ref (dempty seq_compare)

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

val azero = IntInf.fromInt 0
val amillion = IntInf.fromInt 1000000

local open IntInf in

fun term_of_nat n =
  if n < azero then mk_comb (nat_neg, term_of_nat (~ n))
  else if n > amillion then nat_big
  else term_of_nat_aux (toInt n)

end

val seq_empty = mk_var ("seq_empty", alpha);
val seq_cat = mk_var ("seq_cat", alpha3);

fun term_of_seq_nocache seq = case seq of
    [] => seq_empty
  | a :: m => list_mk_comb 
    (seq_cat, [term_of_nat a, term_of_seq_nocache m]);

fun term_of_seq_cache seq = 
  dfind seq (!seqtmd) handle NotFound => 
  let val r =
    case seq of
      [] => seq_empty
    | a :: m => list_mk_comb 
      (seq_cat, [term_of_nat a, term_of_seq_nocache m]);
  in
    seqtmd := dadd seq r (!seqtmd); r
  end
  
fun term_of_seq x = 
  if !use_cache 
  then term_of_seq_cache x
  else term_of_seq_nocache x  
  
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

val nocap_flag = ref false

fun cap tm = 
  if !nocap_flag then tm else
  let val oper = fst (strip_comb tm) in
    mk_comb (cap_tm oper, tm)
  end

(* syntactic *)
fun term_of_prog_nocache (Ins (id,pl)) = 
  if null pl then Vector.sub (operv,id) else
  cap (list_mk_comb (Vector.sub (operv,id), map term_of_prog_nocache pl))

fun term_of_prog_cache (p as (Ins (id,pl))) = 
  dfind p (!progtmd) handle NotFound => 
  let val r =
    if null pl then Vector.sub (operv,id) else
    cap (list_mk_comb (Vector.sub (operv,id), map term_of_prog_cache pl))
  in
    progtmd := dadd p r (!progtmd); r
  end

fun term_of_prog x = 
  if !use_cache 
  then term_of_prog_cache x
  else term_of_prog_nocache x


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
val head_poli = mk_var ("head_poli", alpha2) (* name is important see mkl *)
fun poli_of_board board = mk_comb (head_poli, 
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
   OpenBlas Foreign Function Interface
   ------------------------------------------------------------------------- *)

fun fp_op_default oper embl = Vector.fromList [100.0]
val fp_op_glob = ref fp_op_default

val biais = Vector.fromList ([1.0])

local open Foreign in

fun update_fp_op fileso =
  let
    val lib = loadLibrary fileso
    val fp_op_sym =  getSymbol lib "fp_op"
    val cra = cArrayPointer cDouble;
    val fp_op0 = buildCall3 (fp_op_sym,(cLong,cra,cra),cVoid)
    fun fp_op oper embl =
      let 
        val n = dfind oper opernd
        val dimout =  
          if term_eq oper head_poli then maxmove else (!dim_glob)
        val Xv = Vector.concat (embl @ [biais])
        val X = Array.tabulate (Vector.length Xv, fn i => Vector.sub (Xv,i))
        val Y = Array.array (dimout, 0.0)
        val _ = fp_op0 (n,X,Y)
      in 
        Array.vector Y
      end
  in
    fp_op_glob := fp_op
  end

end (* local *)

(* -------------------------------------------------------------------------
   TNN cache
   ------------------------------------------------------------------------- *)

val maxembn = 100000

fun fp_emb_either tnn oper newembl = 
  if !use_ob
  then (!fp_op_glob) oper newembl
  else fp_emb tnn oper newembl 

fun infer_emb_nocache tnn tm =
  let
    val (oper,argl) = strip_comb tm
    val embl = map (infer_emb_nocache tnn) argl
    val emb = fp_emb_either tnn oper embl
  in
    emb
  end

fun get_targete tnn = infer_emb_nocache tnn 
  (cap (term_of_seq (first_n 16 (!target_glob))))

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

fun rewardf tnn e0 = 0.0

fun player_uniform tnn board = 
  (0.0, map (fn x => (x,1.0)) (#available_movel game board))

fun player_random tnn board = 
  (0.0, map (fn x => (x,random_real ())) (#available_movel game board))

fun player_wtnn_cache tnn board =
  let
    val tm = term_of_join board
    val (_,preboarde) = infer_emb_cache tnn tm
    val prepolie = fp_emb_either tnn prepoli [preboarde]
    val ende = fp_emb_either tnn head_poli [prepolie]
    val pol1 = Vector.fromList (descale_out ende)
    val amovel = #available_movel game board
    val pol2 = map (fn x => (x, Vector.sub (pol1,x))) amovel
  in
    (rewardf tnn preboarde, pol2)
  end

val player_glob = ref player_wtnn_cache

(* -------------------------------------------------------------------------
   Create examples
   ------------------------------------------------------------------------- *)

fun random_step board =
  #apply_move game (random_elem (#available_movel game board)) board

fun random_nstep board = 
  if random_real () < 0.5 then board else random_nstep (random_step board)
  
fun create_exl iprogl =
  let    
    val vect1 = [1.0]
    val vect0 = [0.0]
    val zerov = Vector.tabulate (maxmove, fn _ => 0.0)
    fun create_ex (i,p) = 
      let
        val _ = target_glob := valOf (Array.sub (oseq,i))
        val bml = linearize_safe p
        fun f (board,move) =
           let 
             val newv = Vector.update (zerov, move, 1.0)
             val newl = vector_to_list newv
           in
             (poli_of_board board, newl)
           end
      in
        map f bml
      end
    val _ = use_cache := true
    val r = map create_ex iprogl
    val _ = use_cache := false
  in
    r
  end

(* -------------------------------------------------------------------------
   MKL I/O
   ------------------------------------------------------------------------- *)

fun export_traindata ex = 
  mkl.export_traindata (maxmove,!dim_glob,opernd,operlext) ex

fun read_ctnn sl = mkl.read_ctnn operlext sl

(* -------------------------------------------------------------------------
   XGboost featurizers
   ------------------------------------------------------------------------- *)

fun short_term_of_stack stack =
  let 
    val _ = nocap_flag := true
    val r = term_of_stack stack
    val _ = nocap_flag := false
  in
    r
  end

fun path_of_len2 tm = 
  let 
    val (oper,argl) = strip_comb tm 
    val sl = map (fst o dest_var o fst o strip_comb) argl
    val s = fst (dest_var oper)
  in
    map (fn x => s :: [x]) sl 
  end
  
fun path_of_len3 tm =
  let 
    val (oper,argl) = strip_comb tm     
    val s = fst (dest_var oper)
    val l = List.concat (map path_of_len2 argl)
  in
    map (fn x => s :: x) l 
  end
 
fun all_path3 tm =
  let val (oper,argl) = strip_comb tm in
    [[fst (dest_var oper)]] @ path_of_len2 tm @ path_of_len3 tm @ 
    List.concat (map all_path3 argl)
  end
  
fun fea_of_stack stack = 
  let fun f x = String.concatWith "-" x in 
    map f (all_path3 (short_term_of_stack stack))
  end     

fun suc x = x + 1
local open IntInf in
  val ten = fromInt 10
  fun string_of_nat i n =
    if n < azero then "~" :: string_of_nat i (~n)
    else if n > amillion then ["big"]
    else if n < ten then [toString n ^ "@" ^ its i]
    else (toString (n mod ten) ^ "@" ^ its i) :: 
         string_of_nat (suc i) (n div ten)
end

val progfead = ref (dempty IntInf.compare)

fun init_progfead iprogl =
  let 
    fun compute_freq sol =
      let val freql = dlist 
        (count_dict (dempty prog_compare) (List.concat (map all_subprog sol)))
      in
        dict_sort compare_imax freql
      end
    val l1 = map fst (compute_freq (map snd iprogl))
    val l2 = first_n 5000 (filter (not o depend_on_y) l1) 
    val _ = print_endline 
      ("start evaluation of " ^ its (length l2) ^ " programs")
    val l3 = map_assoc (fn x => exec.penum_limit amillion x 1000) l2
    val _ = print_endline "end evaluation"
    val l4 = number_snd 0 l3
    fun g ((p,seq),n) =
      "p" ^ its n ^ ": " ^ humanf p ^ "\n" ^ 
      string_of_seq (first_n 20 seq) ^ (if length seq > 20 then "..." else "")
    val _ = writel "progfea" (map g l4)
    fun f ((p,seq),(n:int)) = 
      let 
        fun g i = 
          if IntInf.<= (amillion, i) then () else 
          let 
            val oldset = dfind i (!progfead) 
              handle NotFound => eempty Int.compare
            val newset = eadd n oldset
          in
            progfead := dadd i newset (!progfead) 
          end
      in
        app g seq
      end
  in
    progfead := dempty IntInf.compare;
    app f l4
  end

fun fea_of_seq seq = 
  let fun f (a,b) = map (fn x => its a ^ "i-" ^ x) (string_of_nat 0 b) in
    List.concat (map f (number_fst 0 (first_n 16 seq)))
  end

fun export_fea file iprogl =
  let    
    val _ = print_endline "initalizing program features"
    (* val _ = init_progfead iprogl *)
    val _ = print_endline (its (dlength (!progfead)) ^ 
      " numbers with program features")
    val feand = ref (dempty String.compare)
    fun daddf s = if dmem s (!feand) then () else
      feand := dadd s (dlength (!feand)) (!feand)
    val _ = app daddf (map its (#movel game))
    val vect1 = [1.0]
    val vect0 = [0.0]
    val zerov = Vector.tabulate (maxmove, fn _ => 0.0)
    fun create_ex (i,p) = 
      let
        val _ = target_glob := valOf (Array.sub (oseq,i))
        val bml = linearize_safe p
        fun f (board,move) =
           let 
             val amovel = #available_movel game board
             val feal = fea_of_seq (!target_glob) @ fea_of_stack board 
             val feac1 = count_dict (dempty String.compare) feal
             val _ = app daddf (dkeys feac1)
             val feac2 = map (fn (a,b) => its (dfind a (!feand)) ^ ":" ^ 
               its b) (dlist feac1) 
             val feac3 = String.concatWith " " feac2 
             fun g m = (if m = move then "1.0" else "0.0") ^ " " ^ 
               its (dfind (its m) (!feand)) ^ ":1 " ^ feac3 
           in
             map g amovel
           end
      in
        List.concat (map f bml)
      end
    val _ = use_cache := true
    val r = map create_ex iprogl
    val _ = use_cache := false
    val sl = List.concat (map create_ex iprogl)
  in
    writel file sl
  end
 
(* -------------------------------------------------------------------------
   Program features for sequences
   ------------------------------------------------------------------------- *)
  
fun pfea_of_seq seq = 
  let 
    fun pfea x = IntInf.toString x ^ " " ^ 
      String.concatWith " " (map (fn y => "p" ^ its y) 
        (elist (dfind x (!progfead)) handle NotFound => []))
  in
    String.concatWith " " (map pfea (first_n 16 seq))
  end  
  
fun export_seqfea file iprogl =  
  let
    val _ = init_progfead iprogl
    val _ = print_endline "printing program features for each sequence"
    fun create_ex (i,p) = "A" ^ its i ^ ": " ^ 
      pfea_of_seq (valOf (Array.sub (oseq,i)))
  in
    app (fn x => append_endline file 
                 (String.concatWith "\n" (map create_ex x))) 
    (mk_batch_full 100 iprogl)
  end  
  
end (* struct *)

(*
load "tnn"; open kernel aiLib tnn;
time (export_seqfea "seq_with_progfea") (read_iprogl "model/isol295");
time (export_fea "oeis_fea_base10_pfea100") (read_iprogl "model/isol295");
*)

