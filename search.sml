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

val i_alt = ref 0

fun collect_child progd boarde move =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity boarde
  in
    if length l1 <> arity then () else 
    let val p = Ins (move, map #1 (rev l1)) in 
      if depend_on_y p orelse depend_on_z p then () else 
      (incr i_alt ; eaddi (zip_prog p) progd)
    end
  end

fun collect_children progd boarde = app (collect_child progd boarde) movelg

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val threshold_glob = ref 0.000001
val decay = 0.99
val i_glob = ref 0
val imax_glob = ref (Real.round (1.0 / !threshold_glob))

fun equal_pol ((m1,r1),(m2,r2)) = 
  cpl_compare Int.compare Real.compare ((m1,r1),(m2,r2)) = EQUAL
  
fun search_move progd targete (boarde,oldr) (move,r) =
  let val newr = decay * oldr * r in
    if newr < !threshold_glob then () 
    else search_aux progd targete (apply_move move boarde, newr)
  end

and search_aux progd targete (boarde,oldr) = 
  if (!i_glob > !imax_glob)
  then print_endline "search_aux: limit reached" else
  let
    val _ = collect_children progd boarde 
      handle NotFound => raise ERR "collect_children" ""
    val _ = incr i_glob          
    val movel = available_movel boarde
    val f = fp_emb_either (!tnn_glob) 
    val progle = if null boarde then f stack_empty [] else #3 (hd boarde)
    val preboarde = f pair_progseq [progle,targete]
    val prepolie = f prepoli [preboarde]
    val ende = f head_poli [prepolie]
    val pol1 = Vector.fromList (mlNeuralNetwork.descale_out ende)
    val amovel = available_movel boarde
    val pol2 = (map (fn x => (x, Vector.sub (pol1,x))) amovel)
    (*
    val (_,pol2') = player_wtnn_cache (!tnn_glob) (map #1 boarde)
    val _ = if all equal_pol (combine (pol2,pol2')) then ()
            else raise ERR "search_aux" ""
    *)
    val pol3 = normalize_distrib pol2
    val pol4 = if !game.noise_flag then add_noise pol3 else pol3
  in
    app (search_move progd targete (boarde,oldr)) pol4
  end

fun search () = 
  let 
    val progd = ref (eempty Arbint.compare)
    val _ = imax_glob := 10 * Real.round (1.0 / !threshold_glob);
    val _ = i_glob := 0
    val targete = get_targete (!tnn_glob)
    val (_,t) = add_time (search_aux progd targete) ([],1.0)
  in
    print_endline ("tree_size: " ^ its (!i_glob));
    print_endline ("programs: " ^ its (elength (!progd)));
    print_endline ("search time: "  ^ rts_round 2 t ^ " seconds");
    elist (!progd)
  end

end (* struct *)

(* 
PolyML.print_depth 0;
load "search"; open kernel aiLib search; 
tnn_glob := mlTreeNeuralNetwork.random_tnn (tnn.get_tnndim ());
search.threshold_glob := 0.000001;
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
