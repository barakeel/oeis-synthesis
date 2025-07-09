structure kernel :> kernel =
struct

open HolKernel Abbrev boolLib aiLib dir
val ERR = mk_HOL_ERR "kernel"
               
val selfdir = dir.selfdir 

(* -------------------------------------------------------------------------
   Reading flags from config file
   ------------------------------------------------------------------------- *)

val configd = 
  let 
    val sl = readl (selfdir ^ "/config")
    fun f s = SOME (pair_of_list (String.tokens Char.isSpace s)) 
      handle HOL_ERR _ => NONE
  in
    dnew String.compare (List.mapPartial f sl)
  end

fun bflag s = ref (string_to_bool (dfind s configd) handle NotFound => false)
fun bflag_true s = 
  ref (string_to_bool (dfind s configd) handle NotFound => true)
fun iflag s i = ref (string_to_int (dfind s configd) handle NotFound => i) 
fun iflagnoref s i = string_to_int (dfind s configd) handle NotFound => i
fun rflagnoref s i = valOf (Real.fromString (dfind s configd)) 
                     handle NotFound => i

(* main_experiment flags *)
val seq_flag = bflag "seq_flag"
val nomerge_flag = bflag "nomerge_flag"

(* flags for selection of solutions *)
val t_flag = bflag "t_flag"
val sol2_flag = bflag "sol2_flag"
val solm_flag = bflag "solm_flag"
val pareto_flag = bflag "pareto_flag"
val pareto_number = iflagnoref "pareto_number" 0
val optimal_flag = bflag "optimal_flag"
val optimalonly_flag = bflag "optimalonly_flag"
val optimal_coeff = rflagnoref "optimal_coeff" 0.5
val yenum_flag = bflag "yenum_flag"

(* language flags *)
val z_flag = bflag "z_flag"
val extranum_flag = bflag "extranum_flag"
val minimal_flag = bflag "minimal_flag"
val partial_flag = bflag "partial_flag"
val array_flag = bflag "array_flag"
val notarget_flag = bflag "notarget_flag"
val ctree_flag = bflag "ctree_flag"
val wrat_flag = bflag "wrat_flag"
val intl_flag = bflag "intl_flag"
val memo_flag = bflag "memo_flag"
val memo_number = iflagnoref "memo_number" 100000
val prnn_flag = bflag "prnn_flag"
val prnnsum_flag = bflag "prnnsum_flag"
val prnnsum_limit = iflagnoref "prnnsum_limit" 10000
val prnnwidth = iflagnoref "prnnwidth" 5000
val prnntim = iflagnoref "prnntim" 100000


(* search flags *)
val locsearch_flag = bflag "locsearch_flag"
val halfnoise_flag = bflag "halfnoise_flag"
val temperature = rflagnoref "temperature" 1.0
val maxproglen_treesearch = iflagnoref "maxproglen_treesearch" 240
val maxproglen = iflagnoref "maxproglen" 240


(* execution flags *)
  (* this two flags should now be the same *)
val init_timeincr = iflagnoref "init_timeincr" 100000
val short_timeincr = iflagnoref "short_timeincr" 100000
val long_timeincr = iflagnoref "long_timeincr" 100000
val push_limit = iflagnoref "push_limit" 1000000
val maxint_flag = bflag "maxint_flag"
val maxintsize = iflagnoref "maxintsize" 285
  (* deprecated *)
val short_compr = iflagnoref "short_compr" 20
val long_compr = iflagnoref "long_compr" 200

(* training flags *)
val select_cluster = bflag "select_cluster"
val select_random = bflag "select_random"
val select_number = iflagnoref "select_number" 10000
val extra_flag = bflag "extra_flag" (* add extra data for the training *)
val train_multi = iflag "train_multi" 1
val num_epoch = iflagnoref "num_epoch" 100
val learning_rate = rflagnoref "learning_rate" 0.0001
val dim_glob = iflagnoref "dim_glob" 96
val newseq_flag = bflag "newseq_flag" (* other encoding of seq *)
val seqprog_flag = bflag "seqprog_flag" (* training from custom data *)
val revamp_flag = bflag "revamp_flag"

(* external checking flags *)
val reverse_nmtoutput = bflag_true "reverse_nmtoutput"
val reprocess_flag = bflag "reprocess_flag"

(* other flag *)
val reprocess_select_flag = bflag "reprocess_select_flag"
val nooeis_flag = bflag "nooeis_flag"

(* beamsearch experiment *)
val beam_flag = bflag "beam_flag"
val beam_width = iflagnoref "beam_width" 10000
val stop_flag = bflag "stop_flag"

(* experiments *)
val pgen_flag = bflag "pgen_flag"
val _ = if !pgen_flag then notarget_flag := true else ()
val fs_flag = bflag "fs_flag"
val turing_flag = bflag "turing_flag"
val her_flag = bflag "her_flag"
val rps_flag = bflag "rps_flag"
val think_flag = bflag "think_flag"
val run_flag = bflag "run_flag"
val ramsey_flag = bflag "ramsey_flag"
val rams_flag = bflag "rams_flag"
val rams_diff = bflag "rams_diff"
val rams_short = bflag "rams_short"
val rams_noloop = bflag "rams_noloop"
val rams_double = bflag "rams_double"
val rams_dnf = bflag "rams_dnf"
val rams_nicer = bflag "rams_nicer"
val nauto_check = bflag "nauto_check"
val veggy_flag = bflag "veggy_flag"
val hanabi_flag = bflag "hanabi_flag"
val hanabi_short = bflag "hanabi_short"
val arcagi_flag = bflag "arcagi_flag"
val nooeisdata_flag = bflag "nooeisdata_flag"

(* smt flag *)
val smt_flag = bflag "smt_flag"
val noimp_flag = bflag "noimp_flag"
val imp_filter = bflag "imp_filter"
val subz_flag = bflag "subz_flag"
val disable_eval = bflag "disable_eval"
val disable_minimize = bflag "disable_minimize"
val disable_shuffle = bflag "disable_shuffle"
val mydebug = bflag "mydebug"
val fo_flag = bflag "fo_flag"
val skolemize_flag = bflag "skolemize_flag"
val cnf_flag = bflag "cnf_flag"
val split_conj_flag = bflag "split_conj_flag"
val oneline_flag = bflag "oneline_flag"
val altaxiom_flag = bflag "altaxiom_flag"

(* flags originally in rl.sml *)
val expname = ref "test"
val ngen_glob = ref 0

(* match flags *)
val matchback_flag = bflag "matchback_flag"

(* -------------------------------------------------------------------------
   Dictionaries shortcuts
   ------------------------------------------------------------------------- *)

type ('a,'b) dict = ('a, 'b) Redblackmap.dict
fun eaddi x d = d := eadd x (!d)
fun ememi x d = emem x (!d)
fun daddi k v d = d := dadd k v (!d) 
fun dmemi x d = dmem x (!d)
fun dfindo k d = Redblackmap.peek (d,k)
fun ereml kl d = foldl (uncurry erem) d kl;
fun dreml kl d = foldl (uncurry drem) d kl;

(* -------------------------------------------------------------------------
   Other tools
   ------------------------------------------------------------------------- *)

fun range (a,b,f) = List.tabulate (b-a+1,fn i => f (i+a));

fun subsets_of_size_aux n (l,ln) = 
  if n > ln then [] else if n = ln then [l] else
  (
  case l of
    [] => if n = 0 then [[]] else []
  | a :: m => 
    let
      val l1 = map (fn subset => a::subset) 
        (subsets_of_size_aux (n - 1) (m,ln-1))
      val l2 = subsets_of_size_aux n (m,ln-1)
    in
      l1 @ l2
    end  
  )

fun subsets_of_size n l =  subsets_of_size_aux n (l, length l)

val infts = IntInf.toString
val stinf = valOf o IntInf.fromString
val streal = valOf o Real.fromString 

fun ilts il = String.concatWith " " (map its il)
fun stil s = map string_to_int (String.tokens Char.isSpace s)

val timer_glob1 = ref 0.0
val timer_glob2 = ref 0.0
val timer_glob3 = ref 0.0
val timer_glob4 = ref 0.0
val timer_glob5 = ref 0.0

fun inv_cmp cmp (a,b) = cmp (b,a)

fun string_of_var x = fst (dest_var x) 
  handle HOL_ERR _ => raise ERR "string_of_var" (term_to_string x)

fun length_geq l n = length (first_n n l) >= n
fun length_eq l n = case l of 
    [] => n = 0 
  | a :: m => length_eq m (n-1)

fun first_diff cmp l1 l2 = case (l1,l2) of
    ([],_) => NONE
  | (_,[]) => NONE
  | (a1 :: m1, a2 :: m2) => if cmp (a1,a2) = EQUAL 
                            then first_diff cmp m1 m2
                            else SOME (a1,a2);

fun compare_term_size (tm1,tm2) = 
  cpl_compare Int.compare Term.compare 
    ((term_size tm1,tm1),(term_size tm2, tm2))

fun split_pair c s = pair_of_list (String.tokens (fn x => x = c) s)
  handle HOL_ERR _ => raise ERR "split_pair" (Char.toString c ^ ": " ^ s)

(* -------------------------------------------------------------------------
   Sequences
   ------------------------------------------------------------------------- *)

type seq = IntInf.int list
type anum = int
val seq_compare = list_compare IntInf.compare

fun string_of_seq il = String.concatWith " " (map infts il)
fun seq_of_string s = map stinf (String.tokens Char.isSpace s)

val amillion = IntInf.fromInt 1000000
fun gpt_of_int i = 
  if i > amillion then "_" 
  else if i < ~amillion then "~_" 
  else IntInf.toString i

fun gpt_of_seq il = String.concatWith " " (map gpt_of_int il)

fun is_prefix seq1 seq2 = case (seq1,seq2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => if a1 = a2 then is_prefix m1 m2 else false

val target_glob = ref []
val targetn_glob = ref (~1)

(* -------------------------------------------------------------------------
   Program
   ------------------------------------------------------------------------- *)

type id = int
datatype prog = Ins of (id * prog list);
type sol = anum * (int * prog) list

fun prog_compare (Ins(s1,pl1),Ins(s2,pl2)) =
  cpl_compare Int.compare (list_compare prog_compare) ((s1,pl1),(s2,pl2))

fun raw_prog (Ins (id,pl)) =
  if null pl then its id else
  "(" ^ String.concatWith " " (its id :: map raw_prog pl) ^ ")"

fun equal_prog (a,b) = (prog_compare (a,b) = EQUAL)

fun prog_size (Ins(id,pl)) = 1 + sum_int (map prog_size pl)

fun prog_compare_size (p1,p2) =
  cpl_compare Int.compare prog_compare ((prog_size p1,p1),(prog_size p2,p2))

fun all_subprog (p as Ins (_,pl)) = p :: List.concat (map all_subprog pl)

fun all_subcompr (Ins (id,pl)) =
  (if id = 12 then [hd pl] else []) @ List.concat (map all_subcompr pl)

(* -------------------------------------------------------------------------
   Instructions:
   0 1 2 3 4 5 6 7 8    9  10 11 12    13    14   15
   A B C D E F G H I    J    K L M     N     O    P
   0 1 2 + - * / % cond loop x y compr loop2 push pop
   ------------------------------------------------------------------------- *)

val org_operl = [("zero",0),("one",0),("two",0),
  ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
  ("cond",3),("loop",3),("x",0),("y",0),("compr",2),("loop2",5)]

val minimal_operl = 
  [("zero",0),("x",0),("y",0),("suc",1),("pred",1),("loop",3)]

val array_operl = [("zero",0),("one",0),("two",0),
  ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
  ("cond",3),("loop",3),("x",0),("y",0),("array",1),("assign",2)]

val turing_operl = [("zero",0),("one",0),("two",0),
  ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
  ("cond",3),("loope",2),("next",0),("prev",0),("write",1),("read",0)]

val ramsey_operl = [("zero",0),("one",0),("two",0),
  ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
  ("cond",3),("loop",3),("x",0),("y",0),("loop2",5),
  ("push",2),("pop",1),("edge",1)]

val hanabi_operle = if !hanabi_short then 
   [
   ("zero",0,0),("suc",1,0),("five",0,0),
   ("x",0,0),("y",0,0),
   ("ifeq",4,0),("loop",3,1),("loop2",5,2),
   ("push",2,0),("pop",1,0),
   ("clue",0,0),("bomb",0,0),
   ("firework",1,0),("discard",2,0),
   ("mycolh",1,0),("mynumh",1,0),
   ("tmcolh",1,0),("tmnumh",1,0),
   ("tmcol",1,0),("tmnum",1,0),
   ("hist",0,0),("mem",0,0)
   ]
   else
   [
   ("zero",0,0),("one",0,0),("two",0,0),("three",0,0),("four",0,0),("five",0,0),
   ("x",0,0),("y",0,0),
   ("addi",2,0),("mult",2,0),("divi",2,0),("modu",2,0),
   ("ifle",3,0),("ifeq",3,0),("loop",3,1),("loop2",5,2),
   ("push",2,0),("pop",1,0),
   ("clue",0,0),("bomb",0,0),("score",0,0),("turn",0,0),("deckn",0,0),
   ("firework",1,0),("discard",2,0),
   ("mycolh",1,0),("mynumh",1,0),
   ("tmcolh",1,0),("tmnumh",1,0),
   ("tmcol",1,0),("tmnum",1,0),
   ("hist",0,0),("mem",0,0)
   ];
  
val arcagi_operl = org_operl @ [("push",2),("pop",1)] @
  [("equalcolor",4), ("is_out",2), ("is_colori",3), 
   ("is_equal",2), 
   ("input_heigth",0),
   ("input_width",0),
   ("common_height",0), 
   ("common_width",0)]
  
val matchback_operl = org_operl @ [("push",2),("pop",1),("back",1)]

val hanabi_operl = map (fn (a,b,c) => (a,b)) hanabi_operle   
val hanabi_hoargl = map (fn (a,b,c) => c) hanabi_operle

val pgen_operl = map (fn x => (x,1))
  ["mzero","mone","mtwo","maddi","mdiff","mmult","mdivi","mmodu",
   "mcond","mloop","mx","my","mcompr","mloop2"]
   
val ctree_operl = 
  [("push",2),("pop",1),("popr",1),("push2",3),
   ("cdivr",2),("cfloor",1),("cnumer",1),("cdenom",1),("cgcd",2),
   ("cimag",0),("crealpart",1),("cimagpart",1)]
   
val wrat_operl = [("push",2),("pop",1),("while2",5),("divr",2),("floor",1)]
val prnn_operl = [("push",2),("pop",1),("prog",0),("embv",1),("seq",0)] 

(*
val prnn_operl = [("push",2),("pop",1),
  ("prog",0),("proglen",0),("embv",1),("emblen",0),("seq",0),("seqlen",0)] 
*)

val extra_operl =
  if !z_flag then [("z",0),("loop3",7)] 
  else if !extranum_flag
    then [("three",0),("four",0),("five",0),("six",0),("seven",0),("eight",0),
       ("nine",0),("ten",0)] 
  else if !fs_flag then [("perm",1)] 
  else if !pgen_flag then [("seq",1)] @ pgen_operl 
  else if !ctree_flag then ctree_operl 
  else if !wrat_flag then wrat_operl 
  else if !prnn_flag then prnn_operl
  else if !memo_flag then [("push",2),("pop",1)] @ 
                           (if !smt_flag then [("loop2snd",5)] else [])
  else if !intl_flag then [("push",2),("pop",1)] 
  else if !rps_flag then [("hist1",1),("hist2",1)] 
  else if !think_flag then [("think1",1),("think2",1)] 
  else if !run_flag 
    then ("run",1) :: List.tabulate (10, fn i => ("runz" ^ its i, 1)) @ 
      [("runz-",1)]
  else if !seq_flag then [("seq",1)]
  else []

val base_operl = map (fn (x,i) => mk_var (x, rpt_fun_type (i+1) alpha))
  (
  if !matchback_flag then matchback_operl
  else if !arcagi_flag then arcagi_operl 
  else if !hanabi_flag then hanabi_operl
  else if !ramsey_flag then ramsey_operl 
  else if !rams_flag then 
    if !rams_noloop then 
      [("zero",0),("one",0),("two",0),
       ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
       ("cond",3),("x",0),("y",0)]
    else if !rams_short then 
      [("zero",0),("one",0),("two",0),
      ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
      ("cond",3),("loop",3),("x",0),("y",0),("n",0),("loop2",5)]
      @ [("push",2),("pop",1)]
    else if !rams_nicer then 
      [("one",0),("two",0),
       ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
       ("x",0),("y",0)]
    else org_operl @ [("push",2),("pop",1)]
  else if !array_flag then array_operl
  else if !turing_flag then turing_operl
  else if !minimal_flag then minimal_operl
  else org_operl @ extra_operl
  )

(* -------------------------------------------------------------------------
   All operators
   ------------------------------------------------------------------------- *)

val operv = Vector.fromList base_operl
val opersd = map swap
val maxmove = Vector.length operv
val operav = Vector.map arity_of operv
fun arity_of_oper i = Vector.sub (operav,i)
fun name_of_oper i = 
  if i >= Vector.length operv 
  then its i
  else fst (dest_var (Vector.sub (operv,i)))  

val operisl = map_assoc name_of_oper (List.tabulate (Vector.length operv,I))
val opersd = dnew String.compare (map swap operisl)

fun oper_of_name s = dfind s opersd 
  handle NotFound => raise ERR "oper_of_name" s

(* -------------------------------------------------------------------------
   Simple syntactic test
   ------------------------------------------------------------------------- *)

fun contain_id i (Ins (id,pl)) = 
  i = id orelse exists (contain_id i) pl

fun contain_opers s p = case dfindo s opersd of 
    SOME i => contain_id i p 
  | NONE => false

(* -------------------------------------------------------------------------
   Detect dependencies: ho_ariv should match operv
   ------------------------------------------------------------------------- *)

val extra_ho_ariv = 
  if !z_flag then [0,3] 
  else if !extranum_flag then List.tabulate (8, fn _ => 0) 
  else if !fs_flag then [0] 
  else if !pgen_flag 
    then List.tabulate (length pgen_operl + 1, fn _ => 0) 
  else if !ctree_flag 
    then List.tabulate (length ctree_operl, fn _ => 0) 
  else if !wrat_flag then [0,0,3,0,0] 
  else if !intl_flag then List.tabulate (2, fn _ => 0) 
  else if !memo_flag then List.tabulate (2, fn _ => 0) @ 
                          (if !smt_flag then [2] else [])
  else if !prnn_flag then List.tabulate (length prnn_operl, fn _ => 0) 
  else if !think_flag then List.tabulate (2, fn _ => 0) 
  else if !run_flag then List.tabulate (12, fn _ => 0) 
  else if !seq_flag then [0] 
  else []

val ho_ariv = Vector.fromList 
  (
  if !matchback_flag then 
    List.tabulate (9,fn _ => 0) @ [1,0,0,1,2] @ [0,0,0]
  else if !arcagi_flag
    then List.tabulate (9,fn _ => 0) @ [1,0,0,1,2] @ 
         List.tabulate (10,fn _ => 0)
  else if !hanabi_flag 
    then hanabi_hoargl
  else if !ramsey_flag 
    then List.tabulate (9,fn _ => 0) @ [1,0,0,2,0,0,0] 
  else if !turing_flag 
    then List.tabulate (Vector.length operv, fn _ => 0)
  else if !array_flag
    then (List.tabulate (Vector.length operv - 1, fn _ => 0) @ [1])
  else if !minimal_flag 
    then [0,0,0,0,0,1]
  else if !rams_flag then
    if !rams_noloop then 
      List.tabulate (Vector.length operv, fn _ => 0)
    else if !rams_short 
    then List.tabulate (9,fn _ => 0) @ [1,0,0,0,2] @ 
         List.tabulate (2, fn _ => 0)
    else if !rams_nicer then 
         List.tabulate (Vector.length operv, fn _ => 0)
    else List.tabulate (9,fn _ => 0) @ [1,0,0,1,2] @ 
         List.tabulate (2, fn _ => 0) 
  else List.tabulate (9,fn _ => 0) @ [1,0,0,1,2] @ extra_ho_ariv
  )

val _ = if Vector.length ho_ariv <> Vector.length operv
        then raise ERR "ho_ariv" "mismatch with operv"
        else ()
  
fun depend_on v (Ins (id,pl)) = 
  (id = v) orelse 
  let val hari = Vector.sub (ho_ariv,id) in
    if hari = 0 
    then exists (depend_on v) pl
    else exists (depend_on v) (snd (part_n hari pl))
  end

fun find_id s = case dfindo s opersd of SOME id => id | NONE => ~1

val x_id = find_id "x"
val y_id = find_id "y"
val z_id = find_id "z"

fun depend_on_x p = depend_on x_id p
fun depend_on_y p = depend_on y_id p
fun depend_on_z p = depend_on z_id p
fun is_constant p = 
  not (depend_on_x p orelse depend_on_y p orelse depend_on_z p)

fun zeroy (Ins (id,pl)) =
  if id = y_id then (Ins(0,[])) else
  let val hari = Vector.sub (ho_ariv,id) in
    if hari = 0 
    then Ins(id, map zeroy pl)
    else 
      let val (pl1,pl2) = part_n hari pl in
        Ins(id, pl1 @ map zeroy pl2)
      end
  end
  
(* -------------------------------------------------------------------------
   Timer
   ------------------------------------------------------------------------- *)

exception ProgTimeout;
val timeincr = ref short_timeincr
val timelimit = ref (!timeincr)

val abstimer = ref 0
val max_compr_number = ref short_compr (* deprecated *)
val graph = ref []
val graphb = ref 0
val push_counter = ref 0

fun incr_timer () = timelimit := !timelimit + !timeincr
fun init_timer () = (push_counter := 0; abstimer := 0; timelimit := !timeincr)

(* deprecated *)
fun init_fast_test () = 
  (max_compr_number := short_compr; timeincr := short_timeincr)
fun init_slow_test () = 
  (max_compr_number := long_compr; timeincr := long_timeincr)

fun catch_perror f x g = 
  if !prnn_flag then
     (f x handle 
       Empty => g ()
     | Div => g () 
     | ProgTimeout => g () 
     | Overflow => g ()
     | Subscript => g ())
  else
     (f x handle 
       Empty => g ()
     | Div => g () 
     | ProgTimeout => g () 
     | Overflow => g ())
  
fun eval_option f x = 
  let fun g y = (init_timer (); SOME (f y)) in
    catch_perror g x (fn () => NONE)
  end;

fun map_total_aux f acc l = case l of [] => SOME (rev acc) | a :: m =>
  (case f a of NONE => NONE | SOME b => map_total_aux f (b :: acc) m)
 
fun map_total f l = map_total_aux f [] l
 
(* -------------------------------------------------------------------------
   NMT interface
   ------------------------------------------------------------------------- *)

(* printer *)
fun gpt_of_id id = Char.toString (Char.chr (65 + id))
  
fun gpt_of_prog (Ins (id,pl)) = 
  String.concatWith " " (map gpt_of_prog pl @ [gpt_of_id id])

fun tokenl_of_prog (Ins (id,pl)) = 
  List.concat (map tokenl_of_prog pl) @ [id]
 
fun apply_move move board =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 <> arity 
    then raise ERR "apply_move" "arity"
    else Ins (move, rev l1) :: l2
  end 
 
fun prog_of_tokenl tokenl = 
  let val progl = foldl (uncurry apply_move) [] tokenl in
    case progl of [p] => p | _ => raise ERR "prog_of_tokenl" "not a singleton"
  end
  
(* reader *)
fun id_of_gpt s = 
  let val n = Char.ord (valOf (Char.fromString s)) in n - 65 end

fun tokenl_of_gpt s = 
  let val sl = String.tokens Char.isSpace s in map id_of_gpt sl end

fun prog_of_gpt s = prog_of_tokenl (tokenl_of_gpt s)

(* do not raise an error if there are more than one program *)
fun prog_of_tokenl_err tokenl = 
  let val progl = foldl (uncurry apply_move) [] tokenl in
    case progl of [] => raise ERR "prog_of_tokenl" "empty"
      | p :: m => p
  end

(* for reading compressed exp files *)
fun removeSpaces s =
  implode (List.filter (fn c => c <> #" ") (explode s))

fun tokenl_of_gpt_err s = 
  let 
    val s1 = 
      if mem #":" (explode s) 
      then snd (split_pair #":" s)
      else s
    val s2 = removeSpaces s1
    val sl = map Char.toString (explode s2) 
  in  
    map id_of_gpt sl 
  end

fun prog_of_gpt_err s = prog_of_tokenl_err (tokenl_of_gpt s)

(* -------------------------------------------------------------------------
   Storing programs
   ------------------------------------------------------------------------- *)

local open HOLsexp in
  fun enc_prog (Ins x) = pair_encode (Integer, list_encode enc_prog) x
  val enc_progl = list_encode enc_prog
  val enc_proglr = pair_encode (enc_progl, enc_real)  
  fun dec_prog t = 
    Option.map Ins (pair_decode (int_decode, list_decode dec_prog) t)
  val dec_progl = list_decode dec_prog
  val dec_proglr = pair_decode (dec_progl, dec_real)
end
 
fun write_proglrl file r = write_data (HOLsexp.list_encode enc_proglr) file r
fun read_proglrl file = read_data (HOLsexp.list_decode dec_proglr) file
  
local open HOLsexp in
  val enc_iprog = pair_encode (Integer, enc_prog)
  val enc_iprogl = list_encode enc_iprog
  val dec_iprog = pair_decode (int_decode, dec_prog)
  val dec_iprogl = list_decode dec_iprog
  val enc_itprog = pair_encode (Integer, 
    list_encode (pair_encode (Integer, enc_prog)))
  val enc_itprogl = list_encode enc_itprog
  val dec_itprog = pair_decode (int_decode,
    list_decode (pair_decode (int_decode, dec_prog)))
  val dec_itprogl = list_decode dec_itprog
  val enc_bool = String o bts
  val dec_bool = Option.mapPartial (fn x => SOME (string_to_bool x)) 
                 o string_decode
  val enc_aint = String o IntInf.toString       
  val dec_aint = Option.mapPartial IntInf.fromString 
                 o string_decode
  val enc_seql = list_encode (list_encode enc_aint)
  val dec_seql = list_decode (list_decode dec_aint)                             
  val enc_pgen = pair_encode (enc_prog, 
    list_encode (pair_encode (Integer,enc_prog))) 
  val dec_pgen = pair_decode (dec_prog, 
    list_decode (pair_decode (int_decode,dec_prog)))
  val enc_ramsey = pair_encode (pair_encode (Integer, enc_prog), 
                     pair4_encode (Integer,Integer,Integer,Integer))
  val dec_ramsey = pair_decode (pair_decode (int_decode, dec_prog),
     pair4_decode (int_decode,int_decode,int_decode,int_decode))
end



local 
  fun string_of_tp (t,p) = its t ^ " " ^ gpt_of_prog p 
  fun string_of_atpl (anum,tpl) = 
    its anum ^ "," ^ String.concatWith "," (map string_of_tp tpl)
  fun tp_of_string s = 
    let val sl = String.tokens Char.isSpace s in
      (string_to_int (hd sl), prog_of_tokenl (map id_of_gpt (tl sl)))
    end
  fun atpl_of_string s =
    let val sl = String.tokens (fn x => x = #",") s in
      (string_to_int (hd sl), map tp_of_string (tl sl))
    end
in


fun write_itprogl file itprogl = writel file (map string_of_atpl itprogl)
                                 (* write_data enc_itprogl file r *)
fun read_itprogl_human file = map atpl_of_string (readl file)

fun read_itprogl file =
  if hd_string (hd (readl file)) = #"(" 
  then read_data dec_itprogl file
  else read_itprogl_human file 

end (* local *)

(* 
load "kernel"; open kernel aiLib;
val (r1,t1) = add_time read_itprogl (selfdir ^ "/model/itsol843");
val ((),t2) = add_time (write_itprogl (selfdir ^ "/model/itsol843_human")) r1;
val (r2,t3) = add_time read_itprogl (selfdir ^ "/model/itsol843_human");
*)

fun write_progl file pl = writel file (map gpt_of_prog pl)

fun read_progl file = 
  if hd_string (hd (readl file)) = #"(" 
  then read_data dec_progl file
  else map prog_of_gpt (readl file)

type pgen = (prog * (int * prog) list)
fun write_pgen file r = write_data (HOLsexp.list_encode enc_pgen) file r
fun read_pgen file = read_data (HOLsexp.list_decode dec_pgen) file

fun write_seql file r = write_data enc_seql file r
fun read_seql file = read_data dec_seql file

type ramsey = (int * prog) * (int * int * int * int)
fun write_ramseyl file r = write_data (HOLsexp.list_encode enc_ramsey) file r
fun read_ramseyl file = read_data (HOLsexp.list_decode dec_ramsey) file

type hanabi = (int * prog) * IntInf.int

fun write_hanabil file r = 
  let fun f ((sc,p),h) = String.concatWith " "
    (its sc :: infts h :: map its (tokenl_of_prog p))
  in
    writel file (map f r)
  end

fun read_hanabil file =
  let fun f s = 
    let 
      val sl = String.tokens Char.isSpace s 
      val sc = string_to_int (hd sl)
      val p = prog_of_tokenl (map string_to_int (tl (tl sl)))
      val h = stinf (hd (tl sl))
    in
      ((sc,p),h)
    end
  in
    map f (readl file)
  end
  
type arcagi = int * prog * bool * int  
  
fun write_arcagil file r = 
  let fun f (exi,p,b,sc) = String.concatWith " "
    (its exi :: bts b :: its sc :: map its (tokenl_of_prog p))
  in
    writel file (map f r)
  end

fun read_arcagil file =
  let fun f s = 
    let 
      val sl = String.tokens Char.isSpace s
      val exi = string_to_int (List.nth (sl,0))
      val b = string_to_bool (List.nth (sl,1))
      val sc = string_to_int (List.nth (sl,2))
      val p = prog_of_tokenl (map string_to_int (tl (tl (tl sl))))
    in
      (exi,p,b,sc)
    end
  in
    map f (readl file)
  end
 
(* -------------------------------------------------------------------------
   Simple export of sequence program pairs
   ------------------------------------------------------------------------- *)  
 
fun string_of_seqprog (seq,prog) = string_of_seq seq ^ ":" ^ gpt_of_prog prog
fun write_seqprog file seqprogl = writel file (map string_of_seqprog seqprogl)
  
fun seqprog_of_string s = 
  let 
    val (seqs,progs) = pair_of_list (String.tokens (fn x => x = #":") s)
    val seq = seq_of_string seqs
    val prog = prog_of_gpt progs
  in
    (seq,prog)
  end
  
fun read_seqprog file = map seqprog_of_string (readl file)


fun string_of_anumprog (anum,prog) = its anum ^ ":" ^ gpt_of_prog prog
fun write_anumprog file seqprogl = writel file (map string_of_anumprog seqprogl)
  
fun anumprog_of_string s = 
  let 
    val (anums,progs) = pair_of_list (String.tokens (fn x => x = #":") s)
    val anum = string_to_int anums
    val prog = prog_of_gpt progs
  in
    (anum,prog)
  end
  
fun read_anumprog file = map anumprog_of_string (readl file)

(* -------------------------------------------------------------------------
   List of tokens
   ------------------------------------------------------------------------- *)
   
fun prog_of_movel ml = 
  let val progl = foldl (uncurry apply_move) [] ml in
    case progl of [p] => p | _ => raise ERR "prog_of_gpt" "not a singleton"
  end
 
fun prog_of_movelo ml =  
  let val progl = foldl (uncurry apply_move) [] ml in
    case progl of [p] => SOME p | _ => NONE
  end
  handle HOL_ERR _ => NONE

fun valid_topdown_aux argn ml = 
  if argn < 0 then raise ERR "valid_topdown" "" else
  case ml of
    [] => argn = 0
  | token :: newml => 
    let val newargn = argn + (arity_of token - 1) in
      valid_topdown_aux newargn newml
    end
    
fun valid_topdown ml = valid_topdown_aux 1 ml

(* -------------------------------------------------------------------------
   General parallelizer for function : unit -> string -> string
   as long as the function can be named
   ------------------------------------------------------------------------- *)

fun write_string file s = writel file [s]
fun read_string file = singleton_of_list (readl file)
fun write_unit file () = ()
fun read_unit file = ()

fun stringspec_fun_default (s:string) = "default"
val stringspec_fun_glob = ref stringspec_fun_default
val stringspec_funname_glob = ref "kernel.stringspec_fun_default"

val stringspec : (unit, string, string) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "kernel.stringspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    [
    "smlExecScripts.buildheap_dir := " ^ 
       mlquote (!smlExecScripts.buildheap_dir),
    "kernel.stringspec_fun_glob := " ^ (!stringspec_funname_glob)
    ]
    ^ ")"),
  function = let fun f () s = (!stringspec_fun_glob) s in f end,
  write_param = write_unit,
  read_param = read_unit,
  write_arg = write_string,
  read_arg = read_string,
  write_result = write_string,
  read_result = read_string
  }

fun parmap_sl ncore funname sl =
  let  
    val dir = selfdir ^ "/exp/reserved_stringspec"
    val _ = app mkDir_err [(selfdir ^ "/exp"), dir]
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000) 
    val _ = stringspec_funname_glob := funname
    val _ = smlExecScripts.buildheap_dir := dir
    val slo = smlParallel.parmap_queue_extern ncore stringspec () sl
  in
    slo
  end

fun test_fun s = (implode o rev o explode) s

(*
load "kernel"; open aiLib kernel;
val sl = List.tabulate (1000, its);
parmap_sl 2 "kernel.test_fun" sl; 
*)

(* -------------------------------------------------------------------------
   FNV hash
   ------------------------------------------------------------------------- *)

val offset_basis = Word32.fromInt 2166136261
val prime = Word32.fromInt 16777619

fun hashChar (c,h) =
  let val c32 = Word32.fromInt (Char.ord c) in
    Word32.* (Word32.xorb (h, c32), prime)
  end

fun hash s = CharVector.foldl hashChar offset_basis s

fun hashMod i s  =
  Word32.toInt (Word32.mod (hash s, Word32.fromInt i))




end (* struct *)
