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

fun tokenize_seq_aux seq = case seq of
    [] => []
  | [a] => tokenize_aint a  
  | a :: m => tokenize_aint a @ [toksep] @ tokenize_seq_aux m

fun tokenize_seq seq = tokenize_seq_aux (rev (first_n 16 seq))

fun tokenize_stack stack = map snd (linearize_board stack)

fun tokenize_join (seq,board) =
  [tokseq] @ tokenize_seq seq @ [tokprog] @ tokenize_stack board

(* -------------------------------------------------------------------------
   Create objectives and remove last move
   ------------------------------------------------------------------------- *) 

fun mk_obj move = 
  List.tabulate (maxmove, fn x => if x = move then 1.0 else 0.0)
val onev = Vector.tabulate (maxmove, mk_obj)
 
fun add_obj tokenl = case tokenl of 
    [] => raise ERR "add_obj" "empty"
  | [a] => if a < maxmove 
           then [] 
           else raise ERR "add_obj" ""
  | a :: b :: m => 
    if a < maxmove 
    then if b < maxmove andalso b >= 0 
      then (a,SOME b) :: add_obj (b :: m)
      else raise ERR "add_obj" "move"
    else (a,NONE) :: add_obj (b :: m)

(* -------------------------------------------------------------------------
   Add arguments and heads (here arguments are skip connections)
   ------------------------------------------------------------------------- *)

val skipl = [1,5,25]

fun add_arg tokenl =
  let
    val tokenl1 = number_snd 0 tokenl 
    val headl = ref []
    fun g i skip = if i-skip <= 0 then 0 else i-skip
    fun f ((a,bo),i) = if a = tokseq then ([a],[]) else 
      (
      case bo of NONE => ()
               | SOME b => headl := ([tokhead,i], mk_obj b) :: (!headl)
      ;
      (a :: map (g i) skipl, [])
      )
    val r = map f tokenl1
  in
    r @ rev (!headl)
  end 

(* -------------------------------------------------------------------------
   Exporting ot MKL
   ------------------------------------------------------------------------- *)

fun ilts x = String.concatWith " " (map its x)
fun stil x = map string_to_int (String.tokens Char.isSpace x)
fun rlts x = String.concatWith " " (map rts x)

fun cumul_il c il = case il of
    [] => raise ERR "cumul_il" ""
  | [a] => [c]
  | a :: m => c :: cumul_il (a + c) m 

fun create_ex (seq,p) =
  let
    val tokenl = tokenize_join (seq,[p])
    val (dag,obj) = split (add_arg (add_obj tokenl))
  in
    (
    List.concat dag, cumul_il 0 (map length dag),
    List.concat obj, cumul_il 0 (map length obj),
    length dag
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
  
fun wsafe file sl = writel file (check_sl sl)  
  
fun export_traindata datadir nep itsol =
  let
    fun f (a,bl) = (valOf (Array.sub (bloom.oseq,a)),map snd bl)
    val seqprogl = distrib (map f itsol)
    val _ = clean_dir datadir
    val noper = maxmove + 16
    val operlext = List.tabulate (noper,I)
    val nex = length seqprogl
    val (dagl,dagil,objl,objil,sizel) = split_quintuple
      (map create_ex seqprogl);
    fun find_head tok = if tok = tokhead then maxmove else 0 
    fun find_arity tok = 
      if tok = tokseq then 0 else if tok = tokhead then 1 else length skipl
    val dagn = length (List.concat dagl)
    val dagin = length (List.concat dagil)
    val objn = length (List.concat objl)
    val objin = length (List.concat objil)
    fun mk_offset l = map its (cumul_il 0 (map length l))
  in
    wsafe (datadir ^ "/arg.txt") (map its   
      [noper,nex,!dim_glob,dagn,dagin,objn,objin,nep]);
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

fun fp_op_default tok embl = Vector.fromList [100.0]
val fp_op_glob = ref fp_op_default
val biais = Vector.fromList ([1.0])

local open Foreign in

fun update_fp_op fileso =
  let
    val lib = loadLibrary fileso
    val fp_op_sym =  getSymbol lib "fp_op"
    val cra = cArrayPointer cDouble;
    val fp_op0 = buildCall3 (fp_op_sym,(cLong,cra,cra),cVoid)
    fun fp_op tok embl =
      let 
        val dimout = if tok = tokhead then maxmove else (!dim_glob)
        val Xv = Vector.concat (embl @ [biais])
        val X = Array.tabulate (Vector.length Xv, fn i => Vector.sub (Xv,i))
        val Y = Array.array (dimout, 0.0)
        val _ = fp_op0 (tok,X,Y)
      in 
        Array.vector Y
      end
  in
    fp_op_glob := fp_op
  end  

end (* local *)


fun fp_tok tok revembl = 
  let 
    val l = first_n 25 revembl 
    val maxi = length l - 1
    fun f skip = List.nth (l, Int.min (skip-1,maxi))
    val newembl = 
      if tok = tokseq then []
      else if tok = tokhead then [hd l]
      else map f skipl
  in    
    (!fp_op_glob) tok newembl
  end

fun fp_tokl tokl =
  let
    fun loop revembl l = case l of 
        [] => revembl
      | tok :: m => 
        let val newemb = fp_tok tok revembl in
          loop (newemb :: revembl) m
        end
  in
    loop [] tokl
  end
    
end (* struct *)

(*
load "rnn"; open kernel aiLib rnn;
val itsol = read_itprogl "model/itsol209";
val _ = print_endline ("reading itsol " ^ (its (length itsol)));
val _ = print_endline (its (length seqprogl) ^ " examples created");
export_traindata seqprogl;
*)

