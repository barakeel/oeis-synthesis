structure rnn :> rnn =
struct

open HolKernel Abbrev boolLib aiLib smlParallel mcts
  mlNeuralNetwork mlTreeNeuralNetwork kernel human bloom game 

val ERR = mk_HOL_ERR "tnn"

(* -------------------------------------------------------------------------
   Tokenize sequence and programs
   ------------------------------------------------------------------------- *)

val tokbig = maxmove + 1
val tokmin = maxmove + 2
val toksep = maxmove + 3
val starttok = maxmove + 4
val policyhead = maxmove + 5

val natbase = 10
val azero = IntInf.fromInt 0
val amillion = IntInf.fromInt 1000000

fun tokenize_join board = 
  if !notarget_flag 
  then term_of_stack board
  else list_mk_comb (pair_progseq, 
    [term_of_stack board, cap (term_of_seq ())])

fun tokenize_nat n = 
  if n < natbase then [n] else n mod natbase :: talenize_nat (n div natbase)


fun tokenize_aint n = 
  if n < azero then tokmin :: tokenize_aint (~ n)
  else if n > amillion then tokbig
  else tokenize_nat (toInt n)

fun tokenize_seq seq = case seq of
    [] => []
  | [a] => tokenize_aint a  
  | a :: m => tokenize_aint a @ [toksep] @ tokenize_seq m

fun tokenize_stack stack = map snd (linearize_board stack)

fun tokenize_join board =
  if !notarget_flag 
  then tokenize_stack board
  else tokenize_seq (rev (first_n 16 (!target_glob))) @ [starttok] @ 
       tokenize_stack board


(* -------------------------------------------------------------------------
   Add 8 skip connections and policy head: 1,2,4,8,16,32,64,128
   ------------------------------------------------------------------------- *)

fun add_policy tokenl = case tokenl of [] => [] | a :: m => 
  a :: policyhead :: (add_policyhead m)

(* jump because a policy head is interleaved everywhere *)
val mk_argl (oper,x) =
  oper ::
  (if oper = policyhead then [x-1] else 
   map (fn x => if x < 0 then 0) ([x-2,x-4,x-8,x-16,x-32,x-64,x-128,x-256]))

fun add_policyandskip tokenl =
  map mk_argl (number_snd (add_policy tokenl))
 
(* -------------------------------------------------------------------------
   Create objectives (real vector) for each policy head
   ------------------------------------------------------------------------- *) 
 
 val zerov = Vector.tabulate (maxmove, fn _ => ~1.0)
 
 fun mk_obj move =
    
    
    
(* -------------------------------------------------------------------------
   Exporting ot MKL
   ------------------------------------------------------------------------- *)

fun string_to_real x = valOf (Real.fromString x)
fun ilts x = String.concatWith " " (map its x)
fun stil x = map string_to_int (String.tokens Char.isSpace x)
fun rlts x = String.concatWith " " (map rts x)
fun strl x = map string_to_real (String.tokens Char.isSpace x)

fun cumul_il c il = case il of
    [] => raise ERR "cumul_il" ""
  | [a] => [c]
  | a :: m => c :: cumul_il (a + c) m 

fun mk_vect

    
    fun create_ex (i,p) = 
      let
        val _ = target_glob := valOf (Array.sub (oseq,i))
        val bml = linearize_safe p
        val stopex = if not (!stop_flag) then [] else
          [(poli_of_board [p], vector_to_list 
            (Vector.update (zerov, maxmove - 1, 1.0)))]
        fun f (board,move) =
           let 
             val newv = Vector.update (zerov, move, 1.0)

fun create_mklex board =
  let
    fun size_sub x =
      let val (oper,argl) = strip_comb x in (length argl + 1) end
    val sizel1 = map size_sub subtml
    val cumul1 = cumul_il 0 sizel1
    fun enc_obj x = dfind x objd handle NotFound => []
    fun size_obj x = length (dfind x objd) handle NotFound => 0
    val sizel2 = map size_obj subtml
    val cumul2 = cumul_il 0 sizel2 
  in
    (
    List.concat (map enc_sub subtml), cumul1,
    List.concat (map enc_obj subtml), cumul2,
    length subtml
    )
  end

fun split_quintuple l = case l of
    [] => ([],[],[],[],[])
  | (a1,a2,a3,a4,a5) :: m =>
    let val (acc1,acc2,acc3,acc4,acc5) = split_quintuple m in
      (a1 :: acc1, a2 :: acc2, a3 :: acc3, a4 :: acc4, a5 :: acc5)
    end

(* should have a datal for heads and their outputs *)

val buffer_limit = 10000000 - 1 (* same as in tree_template *)

fun check_sl sl = 
  if list_imax (map String.size sl) > buffer_limit
  then (print_endline "line too big"; raise ERR "check_sl" "")
  else sl
  
fun export_traindata (maxmove,dim,opernd,operlext) ex =
  let
    val datadir = kernel.selfdir ^ "/tnn_in_c/data"
    val _ = mkDir_err datadir
    val _ =
      (
      erase_file (datadir ^ "/arg.txt");
      erase_file (datadir ^ "/dag.txt");
      erase_file (datadir ^ "/dagi.txt");
      erase_file (datadir ^ "/obj.txt");
      erase_file (datadir ^ "/obji.txt");
      erase_file (datadir ^ "/size.txt");
      erase_file (datadir ^ "/arity.txt");
      erase_file (datadir ^ "/head.txt")
      )
    val noper = length operlext
    val tmobjll = ex
    val nex = length tmobjll
    val (dagl,dagil,objl,objil,sizel) = split_quintuple
      (map (linearize_ex (dim,opernd)) tmobjll);
    fun find_head tm = 
      let val s = fst (dest_var tm) in  
        if s = "head_poli" then maxmove else 
        if s = "head_value" then 1 else 0
      end
    val dagn = length (List.concat dagl)
    val dagin = length (List.concat dagil)
    val objn = length (List.concat objl)
    val objin = length (List.concat objil)
    fun mk_offset l = map its (cumul_il 0 (map length l))
  in
    writel (datadir ^ "/arg.txt") (map its   
      [noper,nex,dim,dagn,dagin,objn,objin]);
    writel (datadir ^ "/dag.txt") (check_sl (map ilts dagl));
    writel (datadir ^ "/dago.txt") (mk_offset dagl);
    writel (datadir ^ "/dagi.txt") (check_sl (map ilts dagil));
    writel (datadir ^ "/obj.txt") (check_sl (map rlts objl));
    writel (datadir ^ "/objo.txt") (mk_offset objl);
    writel (datadir ^ "/obji.txt") (check_sl (map ilts objil));
    writel (datadir ^ "/size.txt") (map its sizel);
    writel (datadir ^ "/arity.txt") (map (its o arity_of) operlext);
    writel (datadir ^ "/head.txt") (map (its o find_head) operlext)
  end




(* policy head *)
val prepoli = mk_var ("prepoli",alpha2)
val head_poli = mk_var ("head_poli", alpha2) (* name is important see mkl *)
fun poli_of_board board = mk_comb (head_poli, 
  mk_comb (prepoli, term_of_join board))

fun dim_std_alt oper =
  if arity_of oper = 0 
  then [0,!dim_glob] 
  else [!dim_glob * 8, !dim_glob]

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

fun fp_emb_either oper newembl = 
  if !use_ob
  then (!fp_op_glob) oper newembl
  else fp_emb (!tnn_glob) oper newembl 

fun infer_emb_nocache tm =
  let
    val (oper,argl) = strip_comb tm
    val embl = map infer_emb_nocache argl
    val emb = fp_emb_either oper embl
  in
    emb
  end

fun get_targete () = infer_emb_nocache
  (cap (term_of_seq (first_n 16 (!target_glob))))

fun infer_emb_cache tm =
  if is_capped tm
  then
    (
    Redblackmap.findKey (!embd,tm) handle NotFound =>
    let
      val (oper,argl) = strip_comb tm
      val embl = map infer_emb_cache argl
      val (newargl,newembl) = split embl
      val emb = fp_emb_either oper newembl
      val newtm = list_mk_comb (oper,newargl)
    in
      embd := dadd newtm emb (!embd); 
      (newtm,emb)
    end
    )
  else
    let
      val (oper,argl) = strip_comb tm
      val embl = map infer_emb_cache argl
      val (newargl,newembl) = split embl
      val emb = fp_emb_either oper newembl
    in
      (tm,emb)
    end

(* -------------------------------------------------------------------------
   Players
   ------------------------------------------------------------------------- *)

fun rewardf e0 = 0.0

fun player_uniform board = 
  (0.0, map (fn x => (x,1.0)) (#available_movel game board))

fun player_random board = 
  (0.0, map (fn x => (x,random_real ())) (#available_movel game board))

fun player_wtnn_cache board =
  let
    val tm = term_of_join board
    val (_,preboarde) = infer_emb_cache tm
    val prepolie = fp_emb_either prepoli [preboarde]
    val ende = fp_emb_either head_poli [prepolie]
    val pol1 = Vector.fromList (descale_out ende)
    val amovel = #available_movel game board
    val pol2 = map (fn x => (x, Vector.sub (pol1,x))) amovel
  in
    (rewardf preboarde, pol2)
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
    val zerov = Vector.tabulate (maxmove, fn _ => 0.0)
    fun create_ex (i,p) = 
      let
        val _ = target_glob := valOf (Array.sub (oseq,i))
        val bml = linearize_safe p
        val stopex = if not (!stop_flag) then [] else
          [(poli_of_board [p], vector_to_list 
            (Vector.update (zerov, maxmove - 1, 1.0)))]
        fun f (board,move) =
           let 
             val newv = Vector.update (zerov, move, 1.0)
             val newl = vector_to_list newv
           in
             (poli_of_board board, newl)
           end
      in
        stopex @ map f bml
      end
    val _ = use_cache := true
    val r = map create_ex iprogl
    val _ = use_cache := false
  in
    r
  end

fun create_exl_prime progl =
  let
    val zerov = Vector.tabulate (maxmove, fn _ => 0.0)
    fun create_ex p = 
      let
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
    val r = map create_ex progl
    val _ = use_cache := false
  in
    r
  end


fun merge_distrib disl = 
  map average_real (list_combine disl)

fun revamp ex = 
  let 
    val exin = List.concat ex
    val d1 = dappendl exin (dempty Term.compare) 
    val d2 = dmap (fn (k,disl) => merge_distrib disl) d1  
    fun f (tm,dis) = (tm, dfind tm d2)
  in
    map (map f) ex
  end
(* -------------------------------------------------------------------------
   MKL I/O
   ------------------------------------------------------------------------- *)

fun export_traindata ex = 
  mkl.export_traindata (maxmove,!dim_glob,opernd,operlext) 
  (if !notarget_flag then revamp ex else ex)

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
  
fun fea_of_prog p = mk_fast_set String.compare (fea_of_stack [p])

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

