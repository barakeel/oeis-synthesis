structure mizar :> mizar =
struct

open HolKernel Abbrev boolLib aiLib kernel human
val ERR = mk_HOL_ERR "mizar"
type prog = kernel.prog
type sexp = human.sexp

val dim_glob = ref 96
val cj_glob = ref (Ins (0,[]))

fun eaddi x d = d := eadd x (!d)
fun ememi x d = emem x (!d)

fun rm_squote s = 
  if String.size s = 0 then s else
  if String.sub (s,0) = #"'" andalso 
     String.sub (s,String.size s - 1) =  #"'" 
  then String.substring (s,1,String.size s - 2)
  else s;

fun rm_squote_sexp sexp = case sexp of
    Sexp sexpl => Sexp (map rm_squote_sexp sexpl)
  | Stoken s => Stoken (rm_squote s);

fun collect_tokens sexp =  case sexp of
    Sexp sexpl => List.concat (map collect_tokens sexpl)
  | Stoken s => [s];

fun sexp_to_prog operd sexp = case sexp of 
    Sexp (Stoken s :: m) => Ins (dfind s operd, map (sexp_to_prog operd) m)
  | Stoken s => Ins (dfind s operd, [])
  | _ => raise ERR "sexp_to_prog" "not supported"

fun collect_arity_one d (Ins (id,pl)) =
  (
  if dmem id (!d) 
  then 
    if length pl = dfind id (!d) 
    then () 
    else raise ERR "collect_arity" (its id)
  else d := dadd id (length pl) (!d)
  ;
  app (collect_arity_one d) pl
  )

fun collect_arity pl =
  let val d = ref (dempty Int.compare) in
    app (collect_arity_one d) pl; !d
  end

val mizdir = selfdir ^ "/data/lisp"
val filel = listDir mizdir
val seln = 1000
val filel2 = random_subset seln filel;

val _ = print_endline ("Selecting " ^ its seln ^ " problems out of " ^ its (length filel));

fun sexpl_of_pb file =
  map (rm_squote_sexp o parse_sexp) (readl (mizdir ^ "/" ^ file))
val pbl0 = map sexpl_of_pb filel2
val sexpl = List.concat pbl0;
val tokenl = List.concat (map collect_tokens sexpl);
val tokend = count_dict (dempty String.compare) tokenl;
val _ = print_endline ("Number of tokens: " ^ its (dlength tokend))
val tokenl2 = dict_sort compare_imax (dlist tokend);
val opersd = dnew String.compare (number_snd 0 (map fst tokenl2))
val progl = map (sexp_to_prog opersd) sexpl 
val pbl1 = map (map (sexp_to_prog opersd)) pbl0
val _ = print_endline ("Number of parsed problems: " ^ its (length pbl1))

val arityd = collect_arity progl;
fun arity_of_miz opern = dfind opern arityd;


val alpha2 = rpt_fun_type 2 alpha
val alpha3 = rpt_fun_type 3 alpha
val alpha4 = rpt_fun_type 4 alpha

fun mk_oper s = 
  let val a = arity_of_miz (dfind s opersd) in
    mk_var (s, rpt_fun_type (a+1) alpha)
  end
val mizoperv = Vector.fromList (map (mk_oper o fst) tokenl2);
val maxoper = Vector.length mizoperv

val _ = print_endline ("Number of operators: " ^ its maxoper)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

val base = 24
type move = int
val movel = List.tabulate (base * 2,I) @ [base * 2]
val maxmove = length movel
fun string_of_move m = its m

(* -------------------------------------------------------------------------
   Build a list of programs
   ------------------------------------------------------------------------- *)

fun partopt_aux n acc l =
  if n <= 0 then SOME (rev acc,l)
  else if null l then NONE
  else partopt_aux (n - 1) (hd l :: acc) (tl l);
fun partopt n l = partopt_aux n [] l;

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = (prog list * prog list * int list)
val empty_board = ([],[],[])
fun string_of_board (board : board) = "board"
val board_compare = triple_compare
  (list_compare prog_compare)
  (list_compare prog_compare) 
  (list_compare Int.compare)

(* -------------------------------------------------------------------------
   Application of a move to a board
   ------------------------------------------------------------------------- *)

fun eval_il_aux v il = case il of
    [] => raise ERR "eval_il_aux" ""
  | [a] => v * base + a
  | a :: m => eval_il_aux (v * base + a) m 
fun eval_il il = eval_il_aux 0 il

fun id_to_il_aux id = 
  if id < base then [id] else id mod base :: id_to_il_aux (id div base)
fun id_to_il id = rev (id_to_il_aux id)

fun apply_moveo move (axl,pl,il) = 
  if move = 2 * base then 
    (case (pl,il) of ([p],[]) => SOME (p :: axl, [], il)
                               | _ => NONE)
  else if move = 0 andalso not (null il) then NONE 
  else if move >= base then 
    if eval_il (1 :: move - base :: il) >= maxoper then NONE else 
    SOME (axl, pl, move - base :: il) 
  else 
    let val opern = eval_il (move :: il) in
      if opern >= maxoper then NONE else
      case partopt (arity_of_miz opern) pl of 
        NONE => NONE 
      | SOME (pla,plb) => 
         let val newp = Ins (opern, rev pla) in
           SOME (axl,newp :: plb, [])
         end
    end
 
fun apply_move move board = 
  valOf (apply_moveo move board)
  handle Option => raise ERR "apply_move" "option"

(* -------------------------------------------------------------------------
   Available moves
   ------------------------------------------------------------------------- *)

fun available_move board move = isSome (apply_moveo move board)
fun available_movel board = filter (available_move board) movel

(* -------------------------------------------------------------------------
   For debugging
   ------------------------------------------------------------------------- *)

fun random_step board =
  apply_move (random_elem (available_movel board)) board

fun random_board n = funpow n random_step empty_board
  handle Interrupt => raise Interrupt 
    | _ => random_board n

(* -------------------------------------------------------------------------
   Create the sequence of moves that would produce a program p
   ------------------------------------------------------------------------- *)

fun invapp_move (axl,pl,il) = case (axl,pl,il) of 
    ([],[],[]) => NONE
  | (_,_,i :: im) => SOME ((axl,pl,im), base + i) 
  | (_,Ins (id,argl) :: pm,[]) => 
    let val il = id_to_il id in SOME ((axl,rev argl @ pm, tl il), hd il) end
  | (ax :: axm ,[],[]) => SOME ((axm,[ax],[]), 2*base)

fun linearize_aux acc board = case invapp_move board of
    SOME (prev,move) => linearize_aux ((prev,move) :: acc) prev
  | NONE => acc

fun linearize_axl axl = linearize_aux [] (axl,[],[])

fun apply_movel movel board = foldl (uncurry apply_move) board movel

fun linearize_safe pl = 
  let 
    val l = linearize_axl pl
    val movel = map snd l
    val ql = #1 (apply_movel movel empty_board)
  in
    if list_compare prog_compare (pl,ql) = EQUAL then l else
    raise ERR "linearize" ""
  end


(*
(* -------------------------------------------------------------------------
   Board status (all the checking/caching is done during apply move now)
   ------------------------------------------------------------------------- *)

fun status_of (board : board) = Undecided

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = status_of,
  available_movel = available_movel,
  apply_move = apply_move,
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = Int.compare,
  movel = movel
  }

fun player_uniform tnn board = 
  (0.0, map (fn x => (x,1.0)) (available_movel board))

fun mctsobj tnn = 
  {game = game, mctsparam = mctsparam (), player = player_uniform tnn};
*)

(* -------------------------------------------------------------------------
   Convert board into a tree (HOL4 term)
   ------------------------------------------------------------------------- *)

(* two layers *)
fun cap_tm tm = 
  let val name = fst (dest_var tm) in
    mk_var ("cap_" ^ name,alpha2)
  end

fun is_capped tm = 
  let val name = fst (dest_var (fst (strip_comb tm))) in
    String.isPrefix "cap_" name
  end

fun cap_opt tm = 
  if arity_of tm <= 0 
  then NONE
  else SOME (cap_tm tm)

fun cap tm = 
  let val oper = fst (strip_comb tm) in
    mk_comb (cap_tm oper, tm)
  end

(* encoding sequences *)
fun embv_nat i = mk_var ("nat" ^ its i,alpha);
val natoperl = List.tabulate (base,embv_nat);

fun term_of_nat n =
  if n < base andalso n >= 0 then embv_nat n else raise ERR "term_of_nat" ""
val seq_empty = mk_var ("seq_empty", alpha);
val seq_cat = mk_var ("seq_cat", alpha3);
fun term_of_seq seq = case seq of
    [] => seq_empty
  | a :: m => list_mk_comb (seq_cat, [term_of_nat a, term_of_seq m]);
val seqoperl = natoperl @ [seq_empty,seq_cat]

(* prog *)
(* todo: revert to n-ary predicates *)
val prog_empty = mk_var ("prog_empty", alpha);
val prog_cat = mk_var ("prog_cat",alpha3);
val prog_cat8 = mk_var ("prog_cat8", rpt_fun_type 9 alpha);

val cached = ref (dempty prog_compare)
fun term_of_prog (p as (Ins (id,pl))) = 
  dfind p (!cached) handle NotFound => 
  let val r =
    if null pl then Vector.sub (mizoperv,id) else
    cap (list_mk_comb (Vector.sub (mizoperv,id), map term_of_prog pl))
  in
    cached := dadd p r (!cached); r
  end
  
fun term_of_progl_aux progl = case progl of
    [] => prog_empty
  | [a] => term_of_prog a
  | a :: m => list_mk_comb (prog_cat, [term_of_prog a, term_of_progl_aux m])  
  
fun term_of_progl8 progl =
  if length progl < 8 
  then term_of_progl_aux progl
  else list_mk_comb (prog_cat8, (map term_of_prog progl))

fun term_of_progl progl = case progl of
    [] => prog_empty
  | [a] => term_of_prog a
  | a :: m => 
    let val (b,c) = part_n 8 progl in
      list_mk_comb (prog_cat, [term_of_progl8 b, term_of_progl c])
    end

(* together *)
val join_board = mk_var ("join_board", alpha4);
val pair_cj = mk_var ("pair_cj", alpha3);

fun term_of_join (axl,pl,il) = 
  list_mk_comb (pair_cj, 
    [
    term_of_prog (!cj_glob),
    list_mk_comb (join_board,
      [term_of_progl axl, term_of_progl pl, cap (term_of_seq il)])
    ])

(* policy head *)
val prepoli = mk_var ("prepoli",alpha2)
val head_poli = mk_var ("head_poli", alpha2)

fun term_of_board board = mk_comb (head_poli, 
  mk_comb (prepoli, term_of_join board))

(* collecting all possible operators *)
val progoperl = vector_to_list mizoperv @ [prog_empty,prog_cat,prog_cat8]
val progoperlcap = progoperl @ List.mapPartial cap_opt progoperl
val seqoperlcap = seqoperl @ [cap_tm seq_cat, cap_tm seq_empty]
val allcap = [pair_cj, join_board] @ progoperlcap @ seqoperlcap

(* important data *)
val operlext = allcap @ [prepoli,head_poli]
val opernd = dnew Term.compare (number_snd 0 operlext)

(* embedding dimensions *)
fun dim_std_alt oper =
  if arity_of oper = 0 
  then [0,!dim_glob] 
  else [!dim_glob * arity_of oper, !dim_glob]

fun get_tnndim () = 
  map_assoc dim_std_alt allcap @ 
    [(prepoli,[!dim_glob,!dim_glob]),(head_poli,[!dim_glob,maxmove])] 


(* -------------------------------------------------------------------------
   Create examples
   ------------------------------------------------------------------------- *)

fun create_exl pbl =
  let 
    val zerov = Vector.tabulate (maxmove, fn _ => 0.0)
    fun create_ex pl = 
      let
        val _ = cached := dempty prog_compare
        val _ = cj_glob := hd pl
        val bml = linearize_safe (rev (dict_sort prog_compare_size (tl pl)))
          (* (if null (tl pl) then [] else [hd (tl pl)]) *)
        val _ = print_endline (its (length bml))
        fun g (board,move) =
           let 
             val newv = Vector.update (zerov, move, 1.0)
             val newl = vector_to_list newv
           in
             SOME (term_of_board board, newl)
           end 
      in
        if null bml then (print_endline "empty"; NONE) else
        SOME (List.mapPartial g bml)  
      end
  in
    List.mapPartial create_ex pbl
  end

fun export_traindata exl = 
  mkl.export_traindata (maxmove,(!dim_glob),opernd,operlext) exl;

(* 
PolyML.print_depth 0;
load "mizar"; open mizar; 
PolyML.print_depth 0;
val exl = create_exl pbl1;
time export_traindata exl;
*)

end (* struct *)


