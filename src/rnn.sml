structure rnn :> rnn =
struct

open HolKernel boolLib aiLib smlParallel mcts
  mlNeuralNetwork mlTreeNeuralNetwork kernel human bloom game 

val ERR = mk_HOL_ERR "rnn"

(* -------------------------------------------------------------------------
   Tokenize sequence and programs
   ------------------------------------------------------------------------- *)

val tokbig = maxmove
val tokmin = maxmove + 1
val toksep = maxmove + 2
val tokprog = maxmove + 3
val tokseq = maxmove + 4
val tokhead = maxmove + 5
fun mk_toknat n = maxmove + 6 + n

val natbase = 10
val azero = IntInf.fromInt 0
val amillion = IntInf.fromInt 1000000

fun tokenize_nat n = 
  if n < natbase 
  then [mk_toknat n] 
  else mk_toknat (n mod natbase) :: tokenize_nat (n div natbase)

fun tokenize_aint n = 
  if n < azero then tokmin :: tokenize_aint (~ n)
  else if n > amillion then [tokbig]
  else tokenize_nat (IntInf.toInt n)

fun tokenize_seq seq = case seq of
    [] => []
  | [a] => tokenize_aint a  
  | a :: m => tokenize_aint a @ [toksep] @ tokenize_seq m

fun tokenize_stack stack = map snd (linearize_board stack)

fun tokenize_join (seq,board) =
  if !notarget_flag then tokenize_stack board
  else 
    [tokseq] @
    tokenize_seq (rev (first_n 16 seq)) @ 
    [tokprog] @ 
    tokenize_stack board

(* -------------------------------------------------------------------------
   Todo: add all policy heads at the end instead
   create objectives + Remove last move.
   ------------------------------------------------------------------------- *) 

fun mk_obj move = 
  List.tabulate (maxmove, fn x => if x = move then 1.0 else 0.0)
val onev = Vector.tabulate (maxmove, mk_obj)
  
fun add_tokhead tokenl = case tokenl of 
    [] => raise ERR "add_tokhead" "empty"
  | [a] => if a < maxmove then [] else raise ERR "add_tokhead" ""
  | a :: b :: m => 
    if a < maxmove 
    then if b < maxmove andalso b >= 0 
      then (a,[]) :: (tokhead, Vector.sub (onev,b)) :: add_tokhead (b :: m)
      else raise ERR "add_tokhead" "move"
    else (a,[]) :: add_tokhead (b :: m)

(* -------------------------------------------------------------------------
   Number tokens and add arguments (here arguments are skip connections)
   ------------------------------------------------------------------------- *)

fun add_arg tokenl =
  let
    val tokenl1 = number_snd 0 tokenl 
    val tokenl2 = map snd (filter (fn (oper,x) => oper <> tokhead) tokenl1)
    val tokenv = Vector.fromList tokenl2
    val tokend = dnew Int.compare (number_snd 0 tokenl2) 
    fun gety x = dfind x tokend
    fun getx y = Vector.sub (tokenv,y)
    fun g y = if y < 0 then getx 0 else getx y
    fun f (oper,x) =
      if oper = tokseq then [] else
      if oper = tokhead then [x-1] else 
      let val y = gety x in map g [y-1,y-5,y-25] end
  in
    map (fn (oper,x) => oper :: f (oper,x)) tokenl1
  end 

(* -------------------------------------------------------------------------
   Exporting ot MKL
   ------------------------------------------------------------------------- *)

fun myrts s = if hd_string s = #"~" then "-" ^ tl_string s else s
fun ilts x = String.concatWith " " (map its x)
fun stil x = map string_to_int (String.tokens Char.isSpace x)
fun rlts x = String.concatWith " " (map (myrts o rts) x)


fun cumul_il c il = case il of
    [] => raise ERR "cumul_il" ""
  | [a] => [c]
  | a :: m => c :: cumul_il (a + c) m 

fun create_ex (seq,p) =
  let
    val (tokenl,objl) = split ((add_tokhead o tokenize_join) (seq,[p])) 
    val dag = add_arg tokenl
  in
    (List.concat dag, cumul_il 0 (map length dag),
     List.concat objl, cumul_il 0 (map length objl),
     length dag)
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
  
fun wsafe file sl = writel file (check_sl sl)  
  
fun export_traindata itsol =
  let
    fun f (a,bl) = (valOf (Array.sub (bloom.oseq,a)),map snd bl)
    val seqprogl = distrib (map f itsol)
    val datadir = kernel.selfdir ^ "/tnn_in_c/data"
    val _ = clean_dir datadir
    val noper = maxmove + 16
    val operlext = List.tabulate (noper,I)
    val nex = length seqprogl
    val (dagl,dagil,objl,objil,sizel) = split_quintuple
      (map create_ex seqprogl);
    fun find_head tok = if tok = tokhead then maxmove else 0 
    fun find_arity tok = 
      if tok = tokseq then 0 else if tok = tokhead then 1 else 3
    val dagn = length (List.concat dagl)
    val dagin = length (List.concat dagil)
    val objn = length (List.concat objl)
    val objin = length (List.concat objil)
    fun mk_offset l = map its (cumul_il 0 (map length l))
  in
    wsafe (datadir ^ "/arg.txt") (map its   
      [noper,nex,!dim_glob,dagn,dagin,objn,objin]);
    wsafe (datadir ^ "/dag.txt") (map ilts dagl);
    wsafe (datadir ^ "/dago.txt") (mk_offset dagl);
    wsafe (datadir ^ "/dagi.txt") (map ilts dagil);
    wsafe (datadir ^ "/obj.txt") (map rlts objl);
    wsafe (datadir ^ "/objo.txt") (mk_offset objl);
    wsafe (datadir ^ "/obji.txt") (map ilts objil);
    wsafe (datadir ^ "/size.txt") (map its sizel);
    wsafe (datadir ^ "/arity.txt") (map (its o find_arity) operlext);
    wsafe (datadir ^ "/head.txt") (map (its o find_head) operlext)
  end

(* -------------------------------------------------------------------------
   Given an example, 
   do full forward propagation
   do one forward propagation and add to the list of available indices
   ------------------------------------------------------------------------- *)

fun fp_one tok tokenl = 
  
  
end (* struct *)

(*
load "rnn"; open kernel aiLib rnn;

val itsol = read_itprogl "model/itsol209";
val _ = print_endline ("reading itsol " ^ (its (length itsol)));

val _ = print_endline (its (length seqprogl) ^ " examples created");


export_traindata seqprogl;
*)

