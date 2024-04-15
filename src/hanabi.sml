structure hanabi :> hanabi = struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "hanabi"

type exec = int list * int list -> int list

(* -------------------------------------------------------------------------
   Board type
   ------------------------------------------------------------------------- *)

type board = 
  {
  clue : int ref, 
  bomb: int ref, 
  score: int ref, 
  turn: int ref,
  hand1 : ((int*bool)*(int*bool)) list ref,
  hand2 : ((int*bool)*(int*bool)) list ref,
  deck : (int * int) list ref, 
  deckn : int ref,
  firework : int Array.array,
  discard : int Array2.array
  };

fun empty_board () =
  ({
  clue = ref 8,
  bomb = ref 0,
  score = ref 0,
  turn = ref 0,
  hand1 = ref [],
  hand2 = ref [],
  deck = ref [],
  deckn = ref 0,
  firework = Array.tabulate (5,fn _ => ~1),
  discard = Array2.array (5,5,0)
  }: board);

(* -------------------------------------------------------------------------
   Functions called during the execution of the synthesized program
   ------------------------------------------------------------------------- *)


val board_glob = ref (empty_board ());
val myhand_glob = ref (Vector.fromList []);
val tmhand_glob = ref (Vector.fromList []);
val hist_glob = ref [0];
val mem_glob = ref [0];

fun get_clue () = !(#clue (!board_glob))
fun get_bomb () = !(#bomb (!board_glob))
fun get_score () = !(#score (!board_glob))
fun get_turn () = !(#turn (!board_glob))
fun get_deckn () = !(#deckn (!board_glob))
fun get_firework color = 
  Array.sub (#firework (!board_glob), color mod 5)
fun get_discard color number = 
  Array2.sub (#discard (!board_glob), number mod 5, color mod 5)

fun get_mynumh pos =
  let val ((n,b),_) = Vector.sub (!myhand_glob, pos mod 5) in
    if b then n else ~1
  end  
fun get_mycolh pos =
  let val (_,(c,b)) = Vector.sub (!myhand_glob, pos mod 5) in
    if b then c else ~1
  end  

fun get_tmnumh pos =
  let val ((n,b),_) = Vector.sub (!tmhand_glob, pos mod 5) in
    if b then n else ~1
  end  
fun get_tmcolh pos =
  let val (_,(c,b)) = Vector.sub (!tmhand_glob, pos mod 5) in
    if b then c else ~1
  end

fun get_tmnum pos =
  let val ((n,_),_) = Vector.sub (!tmhand_glob, pos mod 5) in n end  
fun get_tmcol pos =
  let val (_,(c,_)) = Vector.sub (!tmhand_glob, pos mod 5) in c end

(* -------------------------------------------------------------------------
   Time limit wrapper
   ------------------------------------------------------------------------- *)

fun checktimer n y = 
  (
  abstimer := !abstimer + n; 
  if !abstimer > !timelimit then raise ProgTimeout else y
  )
  
fun mk_nullf n opf fl = case fl of
    [] => (fn x => checktimer n (opf x))
  | _ => raise ERR "mk_nullf" ""

fun mk_nullf n opf fl = case fl of
    [] => (fn x => checktimer n (opf x))
  | _ => raise ERR "mk_nullf" ""

fun mk_unf n opf fl = case fl of
    [f] => (fn x => checktimer n (opf (f x)))
  | _ => raise ERR "mk_unf" ""

fun mk_binf n opf fl = case fl of
    [f1,f2] => (fn x => checktimer n (opf (f1 x,f2 x)))
  | _ => raise ERR "mk_binf" ""

fun mk_ternf1 opf fl = case fl of
   [f1,f2,f3] => (fn x => checktimer 1 (opf (f1, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf1" ""

fun mk_quintf2 opf fl = case fl of
   [f1,f2,f3,f4,f5] => (fn x => checktimer 1 (opf (f1, f2, f3 x, f4 x, f5 x)))
  | _ => raise ERR "mk_quintf2" ""

(* -------------------------------------------------------------------------
   Hanabi instructions
   ------------------------------------------------------------------------- *)

fun mk_snull f () = [f ()]
fun mk_sun f x = [f (hd x)]
fun mk_sbin f (a,b) = [f (hd a) (hd b)]

val clue_f = mk_nullf 1 (fn (x,y) => mk_snull get_clue ())
val bomb_f = mk_nullf 1 (fn (x,y) => mk_snull get_bomb ())
val score_f = mk_nullf 1 (fn (x,y) => mk_snull get_score ())
val turn_f = mk_nullf 1 (fn (x,y) => mk_snull get_turn ())
val deckn_f = mk_nullf 1 (fn (x,y) => mk_snull get_deckn ())

val firework_f = mk_unf 8 (mk_sun get_firework)
val discard_f = mk_binf 13 (mk_sbin get_discard)

val mynumh_f = mk_unf 10 (mk_sun get_mynumh)
val mycolh_f = mk_unf 10 (mk_sun get_mycolh)
val tmnumh_f = mk_unf 10 (mk_sun get_tmnumh)
val tmcolh_f = mk_unf 10 (mk_sun get_tmcolh)
val tmnum_f = mk_unf 9 (mk_sun get_tmnum)
val tmcol_f = mk_unf 9 (mk_sun get_tmcol)

val hist_f = mk_nullf 1 (fn (x,y) => !hist_glob)
val mem_f = mk_nullf 1 (fn (x,y) => !mem_glob)

(* -------------------------------------------------------------------------
   Arithmetic intructions
   ------------------------------------------------------------------------- *)

val zero_f = mk_nullf 1 (fn (x,y) => [0])
val one_f = mk_nullf 1 (fn (x,y) => [1])
val two_f = mk_nullf 1 (fn (x,y) => [2])
val three_f = mk_nullf 1 (fn (x,y) => [3])
val four_f = mk_nullf 1 (fn (x,y) => [4])
val five_f = mk_nullf 1 (fn (x,y) => [5])
val x_f = mk_nullf 1 (fn (x,y) => x)
val y_f = mk_nullf 1 (fn (x,y) => y)

fun mk_e f (l1,l2) = case (l1,l2) of
    ([],_) => raise Empty
  | (_,[]) => raise Empty
  | (a1 :: m1, a2 :: m2) => (f (a1,a2) :: m1)

val addi_f = mk_binf 1 (mk_e (op +))
val diff_f = mk_binf 1 (mk_e (op -))
val mult_f = mk_binf 1 (mk_e (op *))
val divi_f = mk_binf 5 (mk_e (op div))
val modu_f = mk_binf 5 (mk_e (op mod))

fun ifle_f fl = case fl of
    [f1,f2,f3] => 
    (fn x => checktimer 1 (if hd (f1 x) <= 0 then f2 x else f3 x))
  | _ => raise ERR "mk_iflef" ""

fun ifeq_f fl = case fl of
    [f1,f2,f3] => 
    (fn x => checktimer 1 (if hd (f1 x) = 0 then f2 x else f3 x))
  | _ => raise ERR "mk_ifeqf" ""


fun push_f fl = case fl of
    [f1,f2] => 
    (fn x => (
             incr push_counter; 
             if !push_counter > push_limit then raise Empty else ();
             checktimer 1 (hd (f1 x) :: (f2 x))
             )
             )
  | _ => raise ERR "mk_pushf" ""

fun pop_f fl = case fl of
   [f] => 
   (
   fn x => 
     let val y = case f x of [] => raise Empty | [a] => [a] | a :: m => m in
       checktimer 1 y
     end
   )
  | _ => raise ERR "mk_popf" ""

fun helper f1 f2 n x1 x2 = 
  if n <= 0 then x1 else 
  helper f1 f2 (n-1) (f1 (x1,x2)) (f2 (x1,x2))

fun loop2_f_aux (f1,f2,n,x1,x2) = helper f1 f2 (hd n) x1 x2
val loop2_f = mk_quintf2 loop2_f_aux

fun loop_f_aux (f1,n,x1) = 
  helper f1 (fn (x1,x2) => [(hd x2) + 1]) (hd n) x1 [1]
val loop_f = mk_ternf1 loop_f_aux


(* -------------------------------------------------------------------------
   Execute a hanabi program
   ------------------------------------------------------------------------- *)

val hanabi_list = [
   ("zero",0,0,zero_f),
   ("one",0,0,one_f),
   ("two",0,0,two_f),
   ("three",0,0,three_f),
   ("four",0,0,four_f),
   ("five",0,0,five_f),
   ("x",0,0,x_f),
   ("y",0,0,y_f),
   ("addi",2,0,addi_f),
   ("mult",2,0,mult_f),
   ("divi",2,0,divi_f),
   ("modu",2,0,modu_f),
   ("ifle",3,0,ifle_f),
   ("ifeq",3,0,ifeq_f),
   ("loop",3,1,loop_f),
   ("loop2",5,2,loop2_f),
   ("push",2,1,push_f),
   ("pop",1,1,pop_f),
   ("clue",0,0,clue_f),
   ("bomb",0,0,bomb_f),
   ("score",0,0,score_f),
   ("turn",0,0,turn_f),
   ("deckn",0,0,deckn_f),
   ("firework",1,0,firework_f),
   ("discard",2,0,discard_f),
   ("mycolh",1,0,mycolh_f),
   ("mynumh",1,0,mynumh_f),
   ("tmcolh",1,0,tmcolh_f),
   ("tmnumh",1,0,tmnumh_f),
   ("tmcol",1,0,tmcol_f),
   ("tmnum",1,0,tmnum_f),
   ("hist",0,0,hist_f),
   ("mem",0,0,mem_f)
   ];

val hanabi_execv = Vector.fromList (map (fn (a,b,c,d) => d) hanabi_list)

fun mk_exec_move id fl = Vector.sub (hanabi_execv,id) fl
  
fun mk_exec (p as (Ins (id,pl))) = 
  let val fl = map mk_exec pl in mk_exec_move id fl end

(* -------------------------------------------------------------------------
   Board and moves
   ------------------------------------------------------------------------- *)

val cardl = List.concat (List.tabulate (5,fn i => 
  [(0,i),(0,i),(0,i),(1,i),(1,i),(2,i),(2,i),(3,i),(3,i),(4,i)]));
  
fun init_board cardl ({hand1,hand2,deck,deckn,...}:board)= 
  let 
    val (p1,rest1) = part_n 5 cardl;
    val p1' = map (fn (a,b) => ((a,false),(b,false))) p1;
    val (p2,rest2) = part_n 5 rest1;
    val p2' = map (fn (a,b) => ((a,false),(b,false))) p2;
  in
    hand1 := p1';
    hand2 := p2';
    deck := rest2 @ [(~1,~1),(~1,~1)];
    deckn := length (!deck)
  end;

val colorv = Vector.fromList ["W", "Y", "G", "B", "R"];
fun string_of_card (n,c) = 
  if c=(~1) then "__" else (its (n+1) ^ Vector.sub(colorv,c));

fun string_of_hint ((n,b1),(c,b2)) = 
  if c=(~1) then "__" else 
  (if b1 then its (n+1) else "_") ^
  (if b2 then Vector.sub(colorv,c) else "_");


fun mat_size m = 
  let val (a,b) = Array2.dimensions m in
    if a = b then a else raise ERR "mat_size" ""
  end;

fun mat_to_ll m = 
  let val size = mat_size m in
    List.tabulate (size, fn i => List.tabulate (size,fn j => 
      let val n = Array2.sub (m,i,j) in
        if n = 0 then "___" else
        if n = 1 then "_" ^ string_of_card (i,j) else
        its n ^ string_of_card (i,j)
      end))
  end;

fun string_of_discard a =
  let 
    val ll = mat_to_ll a 
    fun f l = String.concatWith " " l
  in
    quintuple_of_list (map f ll)
  end;

fun print_board  ({clue, bomb, score, turn, hand1, hand2, deck, deckn, firework,
  discard}: board) =
  let 
    val l1 = [!clue,!bomb,!score,!turn,!deckn]
    val l2 = ["clue","bomb","score","turn","deck"]
    val l3 = combine (l1,l2)
    val l4 = map (fn (a,b) => b ^ ":" ^ its a) l3
    val s1 = String.concatWith ", " l4
    val sl2 = map (fn ((n,_),(c,_)) => string_of_card (n,c)) (!hand1);
    val sl3 = map string_of_hint (!hand1);
    val sl4 = map (fn ((n,_),(c,_)) => string_of_card (n,c)) (!hand2);
    val sl5 = map string_of_hint (!hand2);
    val sl6 = map string_of_card (number_snd 0 (array_to_list firework));
    val (hs1,hs2,hs3,hs4,hs5) = string_of_discard discard
    val s2 = String.concatWith " " sl2 ^ "      " ^ hs1
    val s3 = String.concatWith " " sl3 ^ "      " ^ hs2
    val s3' = "                    " ^ hs3
    val s4 = String.concatWith " " sl4 ^ "      " ^ hs4
    val s5 = String.concatWith " " sl5 ^ "      " ^ hs5
    val s6 = String.concatWith " " sl6
  in
    app print_endline [s1,"",s2,s3,s3',s4,s5,"",s6,""]
  end;

val board = empty_board ();
val _ = init_board (shuffle cardl) board;

fun clue_number ({hand1,hand2,clue,turn,...}:board) handn number =
  let 
    val hand = if handn = 0 then hand1 else hand2
    fun f (x as ((n,b),cb)) = if number <> n then x else ((n,true),cb)
    val newhand = map f (!hand)
  in
    decr clue;
    hand := newhand;
    incr turn
  end;

fun clue_color ({hand1,hand2,clue,turn,...}:board) handn color =
  let 
    val hand = if handn = 0 then hand1 else hand2
    fun f (x as (nb,(c,b))) = if color <> c then x else (nb,(c,true))
    val newhand = map f (!hand)
  in
    decr clue;
    hand := newhand;
    incr turn
  end;


val ERR = mk_HOL_ERR "test";  
fun drop_hint ((n,_),(c,_)) = (n,c);

fun get_card_aux acc pos hand = case hand of
    [] => raise ERR "get_card" ""
  | a :: m => 
    if pos <= 0 
    then (rev acc, drop_hint a, m)
    else get_card_aux (a :: acc) (pos - 1) m;
  
fun get_card pos hand = get_card_aux [] pos hand;  
  
fun discard_card ({clue, bomb, score, turn, hand1, hand2, deck, deckn, firework,
  discard}: board) handn pos =
  let
    val hand = if handn = 0 then hand1 else hand2
    val (prevl,(n,c),postl) = get_card pos (!hand)
    val newcard = let val (n',c') = hd (!deck) in ((n',false),(c',false)) end
  in
    Array2.update (discard,n,c,Array2.sub (discard,n,c)+1);
    incr clue;
    hand := newcard :: (prevl @ postl);
    deck := tl (!deck);
    decr deckn;
    incr turn
  end;

fun play_card ({clue, bomb, score, turn, hand1, hand2, deck, deckn, firework,
  discard}: board) handn pos =
  let 
    val hand = if handn = 0 then hand1 else hand2
    val (prevl,(n,c),postl) = get_card pos (!hand)
    val nfire = Array.sub (firework,c)
    val newcard = let val (n',c') = hd (!deck) in ((n',false),(c',false)) end
  in
    if n <> nfire + 1 then
      (
      Array2.update (discard,n,c,Array2.sub (discard,n,c)+1);
      incr bomb;
      hand := newcard :: (prevl @ postl);
      deck := tl (!deck);
      decr deckn;
      incr turn
      )
    else
      (
      Array.update (firework,c,n); 
      incr score;
      hand := newcard :: (prevl @ postl);
      deck := tl (!deck);
      decr deckn;
      incr turn
      )
  end;

fun apply_move (board:board) (ty,i) = 
  let val handn = !(#turn board) mod 2 in
    case ty of
      0 => clue_number board (1 - handn) i
    | 1 => clue_color board (1 - handn) i
    | 2 => discard_card board handn i
    | 3 => play_card board handn i
    | _ => raise ERR "apply_move" ""
  end ; 
  
fun apply_move_msg (board:board) (ty,i) = 
  let 
    val handn = !(#turn board) mod 2 
    val ps = "hand " ^ its (handn + 1)  
  in
    ((
    case ty of
      0 => (print_endline (ps ^ " hints " ^ its (i+1));
      clue_number board (1 - handn) i)
    | 1 => (print_endline (ps ^ " hints " ^ Vector.sub (colorv,i));
      clue_color board (1 - handn) i)
    | 2 => (print_endline (ps ^ " discards at position " ^ its (i+1));
      discard_card board handn i)
    | 3 => (print_endline (ps ^ " plays at position " ^ its (i+1));
      play_card board handn i)
    | _ => raise ERR "apply_move" ""
    ); 
    print_endline "";
    print_board board)
  end;

fun choose_move exec ({turn,clue,hand1,hand2,...}:board) =
  let
    val handn = (!turn) mod 2
    val _ = myhand_glob := Vector.fromList 
      (if handn = 0 then !hand1 else !hand2)
    val _ = tmhand_glob := Vector.fromList
      (if handn = 0 then !hand2 else !hand1)
    val _ = (abstimer := 0; timelimit := !timeincr)
    val movemem = catch_perror exec ([0],[0]) (fn () => [])
  in
    case movemem of [] => NONE | [a] => NONE | _ =>
    let 
      val (move,mem) = part_n 2 movemem 
      val (action',i') = pair_of_list move
      val action = action' mod 4
      val i = i' mod 5
    in
      if action <= 1 andalso !clue <= 0 then NONE else
      if action = 2 andalso !clue >= 8 then NONE else
      (
      mem_glob := mem;
      hist_glob := action :: i :: (!hist_glob);
      SOME (action,i)
      )
    end
  end



fun play_game b p deck = 
  let 
    val appmove = if b then apply_move_msg else apply_move
    val _ = push_counter := 0
    val exec = mk_exec p
    val board = empty_board ()
    val {bomb,deckn,score,turn,...} = board
    val _ = board_glob := board
    val _ = init_board deck board
    val _ = mem_glob := [0]
    val _ = hist_glob := [0]
    fun fail () = (!score) div 2
    fun loopn n = 
      if !bomb >= 3 then fail ()
      else if n <= 0 then !score else
        (
        case choose_move exec board of
          NONE => fail ()
        | SOME move => (appmove board move; loopn (n-1))
        )
    fun loop () =
      if !bomb >= 3 then fail ()
      else if !deckn = 2 then loopn 2 else
        (
        case choose_move exec board of
          NONE => fail ()
        | SOME move => (appmove board move; loop ())
        )
    val sc = loop ()
  in
    (sc,!hist_glob)
  end;

fun string_of_deck deck = 
  let fun f (a,b) = its a ^ "," ^ its b in 
    String.concatWith " " (map f deck)
  end
  
fun deck_of_string s = 
  let
    fun f cards = 
      let val (ns,cs) = 
        pair_of_list (String.tokens (fn x => x = #",") cards)
      in
        (string_to_int ns, string_to_int cs)
      end
  in
    map f (String.tokens Char.isSpace s)
  end
        
fun write_deckl file deckl = writel file (map string_of_deck deckl)
fun read_deckl file = map deck_of_string (readl file)
  
val deckl_glob = 
  if !hanabi_flag 
  then read_deckl (selfdir ^ "/hanabi_deckl10")
  else []

local open IntInf in
fun hash_hist_loop start l = case l of 
    [] => start
  | a :: m => hash_hist_loop (start * 5 + a) m
end

fun concat_hist histl = case histl of
    [] => []
  | [a] => a
  | a :: m => a @ [4,0] @ concat_hist m


fun hanabi_score p = 
  let 
    val l = map (play_game false p) deckl_glob  
    val (scl,histl) = split l 
    val h = hash_hist_loop 1 (map IntInf.fromInt (concat_hist histl))
  in
    (sum_int scl, h)
  end
  
  
end (* struct *)   


(*
load "game"; load "hanabi"; open kernel aiLib human hanabi;

val deckl = List.tabulate (10, fn _ => shuffle cardl);
write_deckl "hanabi_deckl10" deckl;
val deckl' = read_deckl "hanabi_deckl10";
deckl = deckl';


fun f n acc = 
  if n <= 0 then rev acc else
  let 
    val p = game.random_prog 40;
    val deck = aiLib.shuffle cardl;
    val score = play_game false p deck
  in 
    if score <= 0 then f (n-1) acc else f (n-1) (((p,deck),score) :: acc)
  end;

fun g n = f n [];  
 
val (rl,t) = add_time g 10000;

val rl'= first_n 40 (map snd (dict_sort compare_imax rl));

(size,score,fake_score)
10,000^2*100 operations.
Start form 1,000,000.


*)    

