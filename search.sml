structure search :> search =
struct

open HolKernel boolLib aiLib kernel bloom
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
  
fun available_movel boarde = filter available_move boarde movelg

(* -------------------------------------------------------------------------
   Apply a move
   ------------------------------------------------------------------------- *)

val empty_emb = Vector.fromList []

fun exec_fun move l1 l2 =
  let 
    val p = (Ins (move, map #1 (rev l1)))
    (* val _ = test p *)
    (* 
    val emb0 = #3 (hd l2)
    val emb1 = infer_emb opercap [infer_emb oper (map #2 (rev l1))]
    val emb2 = infer_emb cat [emb1,emb0]
    *) 
  in
    (p,empty_emb,empty_emb)
  end 
 
fun apply_move move boarde =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 <> arity 
    then raise ERR "apply_move" ""
    else exec_fun move l1 l2
  end

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val threshold = 1.0 / 1000000.0

fun search_move branch (move,r) =
  let 
    val (boarde,oldr) = hd branch
    val newr = oldr * r 
  in
    if newr < threshold then () else
    let 
      val newboard = apply_move move boarde 
      val newbranch = (newboard :: branch, newr)
    in
      search newbranch
    end
  end
  
and search branch = 
  let 
    val board = hd branch
    val movel = available_movel board  
    val n = length movel
    val pol = map_assoc (fn _ => int_div 1 n) movel
  in
    app (search_move branch) pol 
  end


   

end (* struct *)

(* 
load "exec"; open exec; 
load "human"; open kernel human aiLib;
val p =  parse_human "(loop ( * 2 x) (+ x 2) 1)";
val p = parse_human "(+ (compr (% (- (loop ( * 2 x) (+ x 1) 1) 1) (+ x 2val (l1,t) = add_time (penum p) 5;)) x) 2"; 
humanf p;
val (l1,t) = add_time (penum p) 30;
val isol = read_iprogl "model/isol100"; length isol;
val bbl = map_assoc verify isol;

val lbad1 = filter (not o fst o snd) bbl; length lbad1;
val lbad2 = filter (not o snd o snd) bbl; length lbad2;
val lbad = map fst lbad1;
write_iprogl "lbad" lbad;
val lbad = read_iprogl "lbad";
val lbad3 = map_assoc (verify_wtime 1.0) lbad;

*)
