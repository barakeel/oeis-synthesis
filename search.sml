structure search :> search =
struct

open HolKernel boolLib aiLib kernel bloom mlTreeNeuralNetwork tnn
val ERR = mk_HOL_ERR "search"
type prog = kernel.prog
type emb = real vector

type boarde = (prog * emb * emb) list

(* -------------------------------------------------------------------------
   Noise
   ------------------------------------------------------------------------- *)

fun add_noise prepol =
  let
    val noisel1 = List.tabulate (length prepol, fn _ => random_real ())
    val noisel2 = normalize_proba noisel1
    fun f ((move,polv),noise) =
      let val newpolv = 0.9 * polv + 0.1 * noise in
        (move,newpolv)
      end
  in
    map f (combine (prepol,noisel2))
  end

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

fun collect_child progd boarde move =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity boarde
  in
    if length l1 <> arity then () else 
    let val p = Ins (move, map #1 (rev l1)) in 
      if depend_on_y p orelse depend_on_z p then () else 
      eaddi (zip_prog p) progd
    end
  end

fun collect_children progd boarde = app (collect_child progd boarde) movelg

(* -------------------------------------------------------------------------
   Distributing visit in advance according to policy part of MCTS formula
   ------------------------------------------------------------------------- *)

fun best_move distop = 
  if null distop then raise ERR "best_move" "" else
  let 
    fun loop (maxmove,maxsc) dis = case dis of
        [] => maxmove
      | ((a,b),c) :: m => 
        let val sc = b / (Real.fromInt (c + 1)) in
          if sc > maxsc then loop (a,sc) m else loop (maxmove,maxsc) m
        end
    val ((atop,btop),ctop) = hd distop
    val sctop = btop / (Real.fromInt (ctop + 1))
  in
    loop (atop,sctop) distop
  end     
     
fun inc_bestmove dis = 
  let val i = best_move dis in
    map (fn ((a,b),c) => if a = i then ((a,b),c+1) else ((a,b),c)) dis
  end     
 
fun split_vis nvis dis = 
  let 
    val dis1 = 
      map_assoc (fn (a,b) => Real.floor (b * Real.fromInt nvis)) dis 
    val missing = nvis - sum_int (map snd dis1)
    val dis2 = funpow missing inc_bestmove dis1
  in
    map (fn ((a,b),c) => (a,c)) dis1
  end

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

fun equal_pol ((m1,r1),(m2,r2)) = 
  cpl_compare Int.compare Real.compare ((m1,r1),(m2,r2)) = EQUAL
  
fun search_move progd targete boarde (move,vis) =
  if vis <= 0 then () else
  search_aux vis progd targete (apply_move move boarde)

and search_aux vis progd targete boarde =  
  let
    val _ = collect_children progd boarde 
      handle NotFound => raise ERR "collect_children" ""         
    val movel = available_movel boarde
    val f = fp_emb_either (!tnn_glob) 
    val progle = if null boarde then f stack_empty [] else #3 (hd boarde)
    val preboarde = f pair_progseq [progle,targete]
    val prepolie = f prepoli [preboarde]
    val ende = f head_poli [prepolie]
    val pol1 = Vector.fromList (mlNeuralNetwork.descale_out ende)
    val amovel = available_movel boarde
    val pol2 = (map (fn x => (x, Vector.sub (pol1,x))) amovel)
    val pol3 = normalize_distrib pol2
    val pol4 = if !game.noise_flag then add_noise pol3 else pol3
    val newvis = vis - 1
  in
    if newvis <= 0 then () else
    app (search_move progd targete boarde) (split_vis newvis pol4)
  end

fun search vis = 
  let 
    val progd = ref (eempty Arbint.compare)
    val targete = get_targete (!tnn_glob)
    val (_,t) = add_time (search_aux vis progd targete) []
  in
    print_endline ("programs: " ^ its (elength (!progd)));
    print_endline ("search time: "  ^ rts_round 2 t ^ " seconds");
    elist (!progd)
  end

end (* struct *)

(* 
PolyML.print_depth 0;
load "search"; open kernel aiLib search; 
tnn_glob := mlTreeNeuralNetwork.random_tnn (tnn.get_tnndim ());
search.vis_glob := 2000000;
target_glob := List.tabulate (16,Arbint.fromInt);
tnn.update_fp_op ();
bloom.select_random_target ();
val il1 = search ();


bloom.select_random_target ();
val il2 = search ();
val ili = mk_fast_set (il1 @ il2);
PolyML.print_depth 40;
length il1 + length il2;
length ili;

bloom.select_random_target ();
PolyML.print_depth 0;
val il3 = search ();
PolyML.print_depth 40;
val ili3 = mk_fast_set (ili @ il3);
length il1 + length il2 + lenght il3;
length ili3;


fun test () = let val x = game.random_prog 20 in 
    kernel.prog_compare (x, unzip_prog (zip_prog x)) = EQUAL
  end;
all test (List.tabulate (1000,fn _ => ()));
*)
