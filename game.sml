structure game :> game =
struct

open HolKernel Abbrev boolLib aiLib smlParallel mcts kernel human exec

val ERR = mk_HOL_ERR "game"

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val record_flag = ref false
val progd = ref (eempty prog_compare)
val online_flag = ref false
val bestl_online = ref []
exception ResultP of prog
val target_glob = ref []

(* -------------------------------------------------------------------------
   Parameters
   ------------------------------------------------------------------------- *)

val noise_flag = ref false
val noise_coeff_glob = ref 0.1
val nsim_opt = ref NONE
val time_opt = ref 
  (Real.fromString (dfind "time_opt" configd) handle NotFound => (SOME 600.0))
fun mctsparam () = {
  explo_coeff = 2.0,
  noise = !noise_flag,
  noise_coeff = !noise_coeff_glob, 
  noise_gen = random_real,
  nsim = !nsim_opt : int option, 
  time = !time_opt: real option
  }

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = int
val movelg = List.tabulate (Vector.length operv, I)
val maxmove = length movelg
val move_compare = Int.compare
fun string_of_move x = its x

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = prog list
type player = (board,move) mcts.player
fun string_of_board (board : board) = 
  String.concatWith " | " (map humanf board)
fun board_compare (a,b) = list_compare prog_compare (a,b)

(* -------------------------------------------------------------------------
   Application of a move to a board
   ------------------------------------------------------------------------- *)

(* these functions should match the one in check.sml *)
fun test1 (ncover,p) (oldncover,oldp) = 
  prog_compare_size (p,oldp) = LESS orelse ncover > oldncover 
fun test2 (ncover,p) (oldncover,oldp) =
  prog_compare_size (p,oldp) <> GREATER andalso ncover >= oldncover

fun check_target p target =
  let 
    val _ = init_fast_test ()
    val (b1,n) = coverp_target p (!target_glob)
  in
    if b1 then raise ResultP p else
    if not (all (test1 (n,p)) (!bestl_online)) then () else
    let 
      val _ = bestl_online := filter (not o (test2 (n,p))) (!bestl_online)
      val _ = bestl_online := (n,p) :: (!bestl_online)
      val _ = init_slow_test ()
      val (b2,_) = coverp_target p (!target_glob)
      val _ = init_fast_test ()
    in
      if b2 then raise ResultP p else ()
    end
  end


fun exec_fun p plb =
  (
  if !online_flag andalso not (depend_on_y p) andalso not (depend_on_z p) 
     andalso not (ememi p progd)
    then (eaddi p progd; check_target p (!target_glob))
  else if !record_flag andalso not (depend_on_y p) andalso not (depend_on_z p)
     then eaddi p progd
  else (); 
  SOME (p :: plb)
  )

fun apply_moveo move board =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 <> arity 
    then NONE 
    else exec_fun (Ins (move, rev l1)) l2 
  end

fun apply_move move board = valOf (apply_moveo move board)
fun apply_movel movel board = foldl (uncurry apply_move) board movel

(* -------------------------------------------------------------------------
   Available moves, record all derived programs as a side effect
   ------------------------------------------------------------------------- *)

fun test_move board move =
  let val arity = arity_of_oper move in
    length (first_n arity board) = arity
  end

fun available_movel board =
  if def_flag 
  then filter (test_move board) movelg
  else filter (fn move => isSome (apply_moveo move board)) movelg

(* -------------------------------------------------------------------------
   Random program for testing
   ------------------------------------------------------------------------- *)

fun random_step board =
  apply_move (random_elem (available_movel board)) board

fun random_board n = funpow n random_step []
  handle Interrupt => raise Interrupt 
    | _ => random_board n

fun random_prog n = last (random_board n)

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  available_movel = available_movel,
  apply_move = apply_move,
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = move_compare,
  movel = movelg
  }

(* -------------------------------------------------------------------------
   Create the sequence of moves that would produce a program p
   ------------------------------------------------------------------------- *)

fun invapp_move board = case board of
    [] => NONE
  | Ins (id,argl) :: m => SOME (rev argl @ m, id)

fun linearize_aux acc board = case invapp_move board of
    SOME (prev,move) => linearize_aux ((prev,move) :: acc) prev
  | NONE => acc

fun linearize_board board = linearize_aux [] board

fun linearize p = linearize_aux [] [p]

fun linearize_safe p = 
  let 
    val l = linearize p
    val movel = map snd l
    val q = singleton_of_list (apply_movel movel [])
  in
    if prog_compare (p,q) = EQUAL then l else
    raise ERR "linearize" (humanf p ^ " different from " ^ humanf q)
  end

end (* struct *)
