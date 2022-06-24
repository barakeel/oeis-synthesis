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

fun empty_sobj dim = rlts (List.tabulate (dim, fn _ => 9.0))

fun linearize_ex (maxarity,dim,opernd) tmobjl =
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
       if null l then empty_sobj dim else 
       rlts (l @ List.tabulate (dim - length l, fn _ => 9.0))
  in
    (String.concatWith " " (map (pad_sub o enc_sub) subtml),
     String.concatWith " " (map (pad_obj o enc_obj) subtml),
     length subtml
    )
  end;

fun export_traindata (maxmove,maxarity,dim,opernd,operlext) ex =
  let
    val datadir = kernel.selfdir ^ "/tnn_in_c/data"
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
    val (dagl,objl,sizel) = split_triple 
      (map (linearize_ex (maxarity,dim,opernd)) tmobjll);
    fun find_head tm = if fst (dest_var tm) = "head_poli" then maxmove else 0
  in
    writel (datadir ^ "/arg.txt") (map its [noper,nex,dim]);
    writel (datadir ^ "/dag.txt") dagl;
    writel (datadir ^ "/obj.txt") objl;
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

