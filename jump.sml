structure jump :> jump =
struct

open HolKernel Abbrev boolLib aiLib kernel game;
val ERR = mk_HOL_ERR "jump";

(* -------------------------------------------------------------------------
   Select frequent subprograms in solutions
   ------------------------------------------------------------------------- *)

fun all_subprog_except pd (p as Ins (_,pl)) = 
  if emem p pd
  then [] 
  else p :: List.concat (map (all_subprog_except pd) pl);

fun all_subprog_count pd p =
  dlist (count_dict (dempty prog_compare) (all_subprog_except pd p))

fun best_subprog pd pl =
  let 
    val pnl1 = List.concat (map (all_subprog_count pd) pl)   
    val d = dsum prog_compare pnl1
    fun test (a,b) = 
      let val a' = prog_size a in b >= 3 andalso a' >= 10 end
    val pl2 = map fst (filter test (dlist d))
  in
    if null pl2
    then NONE
    else SOME (last (dict_sort prog_compare_size pl2))
  end

(* -------------------------------------------------------------------------
   Construct the jump tree
   ------------------------------------------------------------------------- *)

datatype jtree = 
  Jleaf of move list |
  Jdict of (bool * (move, jtree) Redblackmap.dict)

val jempty = Jdict (false, dempty Int.compare)

fun jadd movel1 jt = case (jt,movel1) of
    (Jleaf [], _) => jadd movel1 (Jdict (true, dempty Int.compare))
  | (Jleaf (a2 :: m2),_) => 
    jadd movel1 (Jdict (false, dnew Int.compare [(a2,Jleaf m2)]))
  | (Jdict (b,d), []) => Jdict (true, d)
  | (Jdict (b,d), a1 :: m1) =>
    case dfindo a1 d of 
      NONE => Jdict (b, dadd a1 (Jleaf m1) d) 
    | SOME jtchild => Jdict (b, dadd a1 (jadd m1 jtchild) d)

fun create_jtree_board boardl =
  let val movell = map (map snd o linearize_board) boardl in 
    foldl (uncurry jadd) jempty movell
  end

fun create_jtree pl = create_jtree_board (map (fn x => [x]) pl)

(* -------------------------------------------------------------------------
   Propose an auto-completion
   ------------------------------------------------------------------------- *)

fun jfind movel jt = case movel of [] => SOME jt | a1 :: m1 =>
  (
  case jt of
    Jleaf [] => NONE
  | Jleaf (a2 :: m2) => if a1 <> a2 then NONE else jfind m1 (Jleaf m2)  
  | Jdict (b,d) =>
    (case dfindo a1 d of NONE => NONE | SOME jtchild => jfind m1 jtchild)
  )

fun jnext_aux acc jt = case jt of
    Jleaf [] => rev acc
  | Jleaf (a2 :: m2) => jnext_aux (a2 :: acc) (Jleaf m2)  
  | Jdict (b,d) => 
    if b then rev acc else
    (
    case dlist d of
      [(a2,jtchild)] => jnext_aux (a2 :: acc) jtchild
    | _ => rev acc
    )

fun jnext jt = jnext_aux [] jt

fun jump jt board = 
  let val movel = map snd (linearize_board board) in 
    case jfind movel jt of NONE => NONE | SOME newjt =>
    let val contl = jnext newjt in
      case contl of [] => NONE | [a] => NONE | _ => SOME contl
    end
  end

(* -------------------------------------------------------------------------
   Find shortcuts in solutions
   ------------------------------------------------------------------------- *)

fun n_prefix_aux n acc l = if n <= 0 then [] else 
  case l of
    [] => []
  | a :: m => rev (a :: acc) :: n_prefix_aux (n-1) (a :: acc) m

fun n_prefix n l = n_prefix_aux n [] l

fun is_prefix seq1 seq2 = case (seq1,seq2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => if a1 = a2 then is_prefix m1 m2 else false

fun matching_jump jt movel (subboard,i) =
  case jump jt subboard of NONE => NONE | SOME contl =>
    if not (is_prefix contl movel) 
    then NONE
    else SOME ((contl, maxmove + i), length contl)

fun shortcut_board jt movel board =
  if null movel then [] else
  let
    val subboardl = number_snd 0 (n_prefix 5 board)
    val jumpl = List.mapPartial (matching_jump jt movel) subboardl
    val (jump, movei) = 
      if null jumpl 
      then ([hd movel], hd movel)
      else (fst o hd) (dict_sort compare_imax jumpl)
    val newmovel = snd (part_n (length jump) movel)
    val newboard = apply_movel jump board
  in  
    (board,movei) :: shortcut_board jt newmovel newboard
  end
  
fun shortcut jt prog = shortcut_board jt (map snd (linearize prog)) []

  
end (* struct *)

(* -------------------------------------------------------------------------
   Test jump
   ------------------------------------------------------------------------- 

load "jump"; open aiLib kernel human game jump;

val progl = map parse_human ["(- (+ x x) 2)", "(- (+ (+ x x) 1) 2)"];
val jt = create_jtree_board (map (fn x => [x]) progl);
val progl = map snd (read_iprogl (selfdir ^ "/model/isol25"));
val jt = create_jtree 0 progl;
val board = [parse_human "x"];
val newboard = jump jt board;
val prog = random_elem progl;
val l = shortcut jt prog;
prog_size prog;
length l;

val l1 = map_assoc (shortcut jt) progl;
val l2 = filter (fn (a,b) => prog_size a <> length b) l1;

load "jump"; open aiLib kernel human game jump;
val progl = map snd (read_iprogl (selfdir ^ "/model/isol25"));

val pd = ref (eempty prog_compare);
fun loop () =
  case best_subprog (!pd) progl of
    NONE => ()
  | SOME p => (print_endline (humanf p); eaddi p pd; loop ());
load "jump"; open aiLib kernel human game jump;
val progl = map snd (read_iprogl (selfdir ^ "/model/isol25"));
val _ = (pd := eempty prog_compare; loop ());
elength (!pd);

val jt = create_jtree (elist (!pd));
val l1 = map_assoc (shortcut jt) progl;
val l2 = filter (fn (a,b) => prog_size a <> length b) l1;
length l2;
elength (!pd);

val plsmall = filter (fn x => prog_size x < 15) pl;
length plsmall;
*)



