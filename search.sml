structure search :> search =
struct

open HolKernel boolLib aiLib kernel bloom mlTreeNeuralNetwork tnn
val ERR = mk_HOL_ERR "search"
type prog = kernel.prog
type emb = real vector

type progf = Arbint.int * Arbint.int * Arbint.int -> Arbint.int
type boarde = (prog * emb * emb) list
type branch = (boarde * real) list

(* -------------------------------------------------------------------------
   Available moves
   ------------------------------------------------------------------------- *)

val movelg = List.tabulate (Vector.length operv, I)  

fun available_move boarde move =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity boarde 
  in
    length l1 = arity 
  end
  
fun available_movel boarde = filter (available_move boarde) movelg

(* -------------------------------------------------------------------------
   Apply a move
   ------------------------------------------------------------------------- *)

val tnn_glob = ref (dempty Term.compare)
val empty_emb = Vector.fromList []

fun exec_fun move l1 l2 =
  let 
    val f = fp_emb_either (!tnn_glob)
    val p = (Ins (move, map #1 (rev l1)))
    (* val _ = test p *)
    val oper = Vector.sub (operv,move)
    val emb1 = 
      if arity_of oper <= 0 
      then f oper []
      else f (cap_tm oper) [f oper (map #2 (rev l1))]
    val emb2 = 
      if null l2 then emb1 else
      f (cap_tm stack_cat) [f stack_cat [emb1, #3 (hd l2)]]
  in
    (p,emb1,emb2) :: l2
  end 
 
fun apply_move move boarde =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity boarde
  in
    if length l1 <> arity 
    then raise ERR "apply_move" ""
    else exec_fun move l1 l2
  end

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val threshold_glob = ref (1.0 / 1000000.0)
val i_glob = ref 0

fun search_move (boarde,oldr) (move,r) =
  let val newr = oldr * r in
    if newr < !threshold_glob then () 
    else search (apply_move move boarde, newr)
  end
  
and search (boarde,oldr) = 
  let
    val _ = incr i_glob
    val movel = available_movel boarde
    val f = fp_emb_either (!tnn_glob) 
    val preboarde = 
      if null boarde then f stack_empty [] else #3 (hd boarde)
    val prepolie = f prepoli [preboarde]
    val ende = f head_poli [prepolie]
    val pol1 = Vector.fromList (mlNeuralNetwork.descale_out ende)
    val amovel = available_movel boarde
    val pol2 = normalize_distrib 
      (map (fn x => (x, Vector.sub (pol1,x))) amovel)
  in
    app (search_move (boarde,oldr)) pol2
  end


   

end (* struct *)

(* 
load "search"; open kernel aiLib search; 
tnn_glob := mlTreeNeuralNetwork.random_tnn (tnn.get_tnndim ());
tnn.use_ob := false;
time search ([],1.0);
!i;

*)
