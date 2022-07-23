structure mkl :> mkl =
struct

open HolKernel Abbrev boolLib aiLib smlParallel mcts
  mlNeuralNetwork mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "mkl"
type tnn = mlTreeNeuralNetwork.tnn

(* -------------------------------------------------------------------------
   I/O utils
   ------------------------------------------------------------------------- *)

fun string_to_real x = valOf (Real.fromString x)
fun ilts x = String.concatWith " " (map its x)
fun stil x = map string_to_int (String.tokens Char.isSpace x)
fun rlts x = String.concatWith " " (map rts x)
fun strl x = map string_to_real (String.tokens Char.isSpace x)

(* -------------------------------------------------------------------------
   Export training examples to MKL 
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

fun cumul_il c il = case il of
    [] => raise ERR "cumul_il" ""
  | [a] => [c]
  | a :: m => c :: cumul_il (a + c) m 

fun linearize_ex (dim,opernd) tmobjl =
  let
    val objd = dnew Term.compare tmobjl
    val subtml = order_subtm (map fst tmobjl);
    val indexd = dnew Term.compare (number_snd 0 subtml);
    fun enc_sub x = 
      let val (oper,argl) = strip_comb x in
        dfind oper opernd :: map (fn x => dfind x indexd) argl
      end
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


(* -------------------------------------------------------------------------
   Reading TNN produced by MKL
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

fun read_ctnn operlext sl = 
  dnew Term.compare (combine (operlext,read_ctnn_aux sl)) 

end (* struct *)

