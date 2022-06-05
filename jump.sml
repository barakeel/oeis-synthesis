structure jump :> jump =
struct

open HolKernel Abbrev boolLib aiLib kernel game;
val ERR = mk_HOL_ERR "jump";
type move = int


(* -------------------------------------------------------------------------
   Select frequent subsequences in solutions starting with 
   ------------------------------------------------------------------------- *)

(* excludes empty board *)
fun all_subboard_aux revboard = case revboard of
    [] => []
  | a :: m => revboard :: all_subboard_aux m

fun all_subboard board = map rev (all_subboard_aux (rev board))

fun all_subboard_trace p =
  let 
    val board = [p]
    val boardl = map fst (linearize_board board) 
  in 
    mk_fast_set (#board_compare game) 
    (List.concat (map all_subboard (board :: boardl)))
  end

fun count_subboard pl =
  let 
    val bl = List.concat (map all_subboard_trace pl)   
    val d = count_dict (dempty (#board_compare game)) bl
  in
    dict_sort compare_imax (dlist d)
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

fun create_jtree pl =
  let 
    val boardnl = count_subboard pl
    val boardl = map fst (filter (fn x => snd x >= 100) boardnl)
    val movell = map (map snd o linearize_board) boardl
  in 
    foldl (uncurry jadd) jempty movell
  end

(* -------------------------------------------------------------------------
   Auto-complete until the next split
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
      case contl of [] => NONE | [a] => NONE | _ => 
        SOME (apply_movel contl board)
    end
  end

fun is_prefix seq1 seq2 = case (seq1,seq2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => if a1 = a2 then is_prefix m1 m2 else false

fun compress jt targetboard board =
  let 
    val movel = map snd (linearize_board targetboard) 
    val subboardl = first_n 5 (rev (all_subboard board))
  in  
    case jfind movel jt of NONE => NONE | SOME newjt =>
    let val contl = jnext newjt in
      case contl of [] => NONE | [a] => NONE | _ => 
        if is_prefix  
        then 
        SOME (apply_movel contl board)
    end
  end

end (* struct *)

(* -------------------------------------------------------------------------
   Test jump
   ------------------------------------------------------------------------- 

load "jump"; open aiLib kernel human game jump;

val progl = map parse_human ["(- (+ x x) 2)", "(- (+ (+ x x) 1) 2)"];
val progl = map snd (read_iprogl (selfdir ^ "/model/isol25"));
val jt = create_jtree progl;
val board = [parse_human "2 + ( * x y)"];
val newboard = jump jt board;

*)



