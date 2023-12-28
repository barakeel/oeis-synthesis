structure kernel :> kernel =
struct

open HolKernel Abbrev boolLib aiLib dir;
val ERR = mk_HOL_ERR "kernel";
               
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

(* search flags *)
val locsearch_flag = bflag "locsearch_flag"
val halfnoise_flag = bflag "halfnoise_flag"
val temperature = rflagnoref "temperature" 1.0
val maxproglen = iflagnoref "maxproglen" 240

(* execution flags *)
  (* this two flags should now be the same *)
val init_timeincr = iflagnoref "init_timeincr" 1000
val short_timeincr = iflagnoref "short_timeincr" 100000
val long_timeincr = iflagnoref "long_timeincr" 100000
val push_limit = iflagnoref "push_limit" 1000000
  (* deprecated *)
val maxintsize = iflagnoref "maxintsize" 285
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


val smartselect_flag = bflag "smartselect_flag"

(* flags originally in rl.sml *)
val expname = ref "test"
val ngen_glob = ref 0

(* -------------------------------------------------------------------------
   Default memory limit for parallel processes (8GB)
   ------------------------------------------------------------------------- *)

val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
  (string_to_int (dfind "search_memory" configd) handle NotFound => 8000) 

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

(* -------------------------------------------------------------------------
   Sequences
   ------------------------------------------------------------------------- *)

type seq = IntInf.int list
type anum = int
val seq_compare = list_compare IntInf.compare

fun string_of_seq il = String.concatWith " " (map IntInf.toString il)
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

fun write_itprogl file r = write_data enc_itprogl file r
fun read_itprogl file = read_data dec_itprogl file

type pgen = (prog * (int * prog) list)
fun write_pgen file r = write_data (HOLsexp.list_encode enc_pgen) file r
fun read_pgen file = read_data (HOLsexp.list_decode dec_pgen) file

fun write_progl file r = write_data enc_progl file r
fun read_progl file = read_data dec_progl file

fun write_seql file r = write_data enc_seql file r
fun read_seql file = read_data dec_seql file

type ramsey = (int * prog) * (int * int * int * int)
fun write_ramseyl file r = write_data (HOLsexp.list_encode enc_ramsey) file r
fun read_ramseyl file = read_data (HOLsexp.list_decode dec_ramsey) file


(* -------------------------------------------------------------------------
   Instructions:
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
  else if !memo_flag then [("push",2),("pop",1)]
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
  if !ramsey_flag then ramsey_operl 
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
  else if !memo_flag then List.tabulate (2, fn _ => 0) 
  else if !prnn_flag then List.tabulate (length prnn_operl, fn _ => 0) 
  else if !think_flag then List.tabulate (2, fn _ => 0) 
  else if !run_flag then List.tabulate (12, fn _ => 0) 
  else if !seq_flag then [0] 
  else []

val ho_ariv = Vector.fromList 
  (
  if !ramsey_flag 
    then List.tabulate (9,fn _ => 0) @ [1,0,0,2,0,0,0] 
  else if !turing_flag 
    then List.tabulate (Vector.length operv, fn _ => 0)
  else if !array_flag
    then (List.tabulate (Vector.length operv - 1, fn _ => 0) @ [1])
  else if !minimal_flag 
    then [0,0,0,0,0,1]
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

end (* struct *)
