structure search :> search =
struct

open HolKernel boolLib aiLib kernel bloom mlTreeNeuralNetwork tnn exec check bloom
val ERR = mk_HOL_ERR "search"
type emb = real vector

(* first embedding is prog embedding, second is stack *)
type boarde = (kernel.prog * exec.exec * emb * emb) list

(* type boarde = (kernel.prog * exec.exec * emb * emb) list * emb list *)

val randsearch_flag = ref false

(* -------------------------------------------------------------------------
   Counting tree
   ------------------------------------------------------------------------- *)

fun update_vector v n k =
  if n >= Vector.length v 
  then Vector.concat [v, 
    Vector.tabulate (n - Vector.length v, fn _ => NONE), 
    Vector.fromList [SOME k]]
  else Vector.update (v,n,SOME k)

datatype ctree = 
  Cleaf of int list |
  Cvect of int * ctree option vector 

val vempty = Vector.fromList []
val ctempty = Cvect (0,vempty)
val ct_glob = ref ctempty 
 
fun cadd seq ct = case (ct,seq) of
    (Cleaf [], _) => 
    cadd seq (Cvect (1, vempty))
  | (Cleaf (a2 :: m2), _) => 
    cadd seq (Cvect (1, update_vector vempty a2 (Cleaf m2)))
  | (Cvect (n,v), []) => Cvect (n+1, v)
  | (Cvect (n,v), a1 :: m1) =>
    let val cto = Vector.sub (v,a1) handle Subscript => NONE in
      case cto of
        NONE => Cvect (n+1, update_vector v a1 (Cleaf m1)) 
      | SOME newct => Cvect (n+1, update_vector v a1 (cadd m1 newct))
    end
  
fun crm seq ct = case (ct,seq) of
    (Cleaf seq2, _) => 
    if seq <> seq2 
    then raise ERR "crm" "sequence not found 1" 
    else ctempty
  | (Cvect (n,v), []) => 
    if n-1 < 0 
    then raise ERR "crm" "sequence not found 2"
    else if n-1 <= 0 then ctempty else Cvect (n-1,v)
  | (Cvect (n,v), a1 :: m1) =>
    let val cto = Vector.sub (v,a1) handle Subscript => NONE in
      case cto of
        NONE => raise ERR "crm" "sequence not found 3"
      | SOME newct => Cvect (n-1, update_vector v a1 (crm m1 newct))
    end

fun clist ct =
  let 
    val acc = ref [] 
    fun clist_aux revprefix ct = case ct of
      Cleaf _ => ()
    | Cvect (n,v) => if n < 20 then () else
      let 
        val _ = acc := (rev revprefix, n) :: !acc
        val l1 = number_snd 0 (vector_to_list v)
        fun f (newcto,a) = case newcto of
            NONE => () 
          | SOME newct => clist_aux (a :: revprefix) newct
      in
        app f l1   
      end
  in 
    clist_aux [] ct; !acc 
  end

fun cfind seq ct = case (ct,seq) of
    (Cleaf _, _) => raise ERR "cfind" "unexpected"
  | (Cvect (n,v), []) => ct
  | (Cvect (n,v), a1 :: m1) =>
    let val cto = Vector.sub (v,a1) handle Subscript => NONE in
      case cto of
        NONE => ct
      | SOME (Cleaf _) => ct
      | SOME (newct as Cvect (n,_)) => 
        if n < 100 then ct else cfind m1 newct  
    end

fun cnum cto = case cto of
    NONE => 0
  | SOME (Cleaf _) => 1
  | SOME (Cvect (n,v)) => n
  
fun cproba ct = case ct of
    Cleaf _ => raise ERR "cproba" "unexpected"
  | Cvect (n,v) => Vector.map (fn x => int_div (cnum x) n) v
    
fun cplayer ct board =
  let 
    val ml = map snd (rev (game.linearize_board board))
    val v = cproba (cfind ml ct)
    fun f x = (x, Vector.sub (v,x) handle Subscript => 0.0)
  in
    (0.0, map f (#available_movel game.game board))
  end


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

val empty_emb = Vector.fromList []

fun exec_fun (move,exec) l1 l2 =
  let 
    val f = fp_emb_either
    val p = (Ins (move, map #1 (rev l1)))
  in
    if !randsearch_flag orelse !simple_flag 
      then (p,exec,empty_emb,empty_emb) :: l2 else
    let
      val oper = Vector.sub (operv,move)
      val emb1 = 
        if arity_of oper <= 0 
        then f oper []
        else f (cap_tm oper) [f oper (map #3 (rev l1))]
      val emb2 = 
        if null l2 then emb1 else
        f (cap_tm stack_cat) [f stack_cat [emb1, #4 (hd l2)]]
    in
      (p,exec,emb1,emb2) :: l2
    end
  end

fun apply_move (move,exec) boarde =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity boarde
  in
    if length l1 <> arity 
    then raise ERR "apply_move" ""
    else exec_fun (move,exec) l1 l2
  end

val node_counter = ref 0
val prog_counter = ref 0

fun collect_child boarde move =
  let 
    val _ = incr node_counter
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity boarde
  in
    if length l1 <> arity then NONE else
    let
      val p = Ins (move, map #1 (rev l1))
      val exec = mk_exec_move move (map #2 (rev l1))  
    in 
      if !locsearch_flag andalso null l2 andalso not (depend_on_y p)
      then (incr prog_counter; 
            checkonline (p,exec); 
            SOME (move, cache_exec exec))
      else SOME (move,exec)
    end
  end

fun collect_children boarde = case boarde of
    [(p,exec,a,b)] => 
    let 
      val _ = if not (!locsearch_flag) 
              then (incr prog_counter; 
                    if !ramsey_flag then checkonline_ramsey (p,exec)
                    else if !hadamard_flag then checkonline_hdm (p,exec)
                    else if !prime_flag then ignore (checkonline_prime (p,exec))
                    else checkonline (p,exec))
              else ()
      val newboarde = boarde
    in
      (newboarde, List.mapPartial (collect_child newboarde) movelg)
    end
  | _ => (boarde, List.mapPartial (collect_child boarde) movelg)
   

(* -------------------------------------------------------------------------
   Distributing visits in advance according to policy part of MCTS formula
   ------------------------------------------------------------------------- *)

fun best_move distop = 
  if null distop then raise ERR "best_move" "" else
  let 
    fun loop (maxmove,maxsc) dis = case dis of
        [] => maxmove
      | ((a,b),c) :: m => 
        let val sc = b / (Real.fromInt (c + 1)) in
          if sc > maxsc then loop (fst a,sc) m else loop (maxmove,maxsc) m
        end
    val ((atop,btop),ctop) = hd distop
    val sctop = btop / (Real.fromInt (ctop + 1))
  in
    loop (fst atop,sctop) distop
  end     
     
fun inc_bestmove dis = 
  let val i = best_move dis in
    map (fn ((a,b),c) => if fst a = i then ((a,b),c+1) else ((a,b),c)) dis
  end     
 
fun split_vis nvis dis = 
  let 
    fun rm_polv ((a,b),c) = (a,c)
    fun f (_,b) =
      let val c = Real.floor (b * Real.fromInt nvis) in
        if c < 0 then 0 else if c >= nvis then nvis - 1 else c
      end
    val dis1 = map_assoc f dis 
    val missing = nvis - sum_int (map snd dis1)
    val dis2 = funpow missing inc_bestmove dis1
  in
    map rm_polv dis1
  end
  
(* -------------------------------------------------------------------------
   Allocate time in advance according to the prior probabilities
   ------------------------------------------------------------------------- *)  
   
fun split_tim (torg,tinc) dis = 
  let 
    fun rm_polv ((a,b),c) = (a,c)
    val sum = ref 0.0
    fun f (_,b) =
      let 
        val c = b * tinc
        val newinc = if c < 0.0 then 0.0 else if c >= tinc then tinc else c
        val neworg = torg + !sum
        val _ = sum := !sum + newinc
      in  
        (neworg,newinc)
      end
  in
    map rm_polv (map_assoc f dis)
  end
  
(* -------------------------------------------------------------------------
   Create a policy from a targete and boarde
   ------------------------------------------------------------------------- *)

fun create_pol targete boarde mfl =
  if !randsearch_flag 
    then normalize_distrib (map (fn x => (x, random_real ())) mfl)
  else
  if !simple_flag then
    let 
      val ml = map snd (rev (game.linearize_board (map #1 boarde)))
      val v = cproba (cfind ml (!ct_glob))
      fun f x = (x, (Vector.sub (v,fst x) handle Subscript => 0.0))
      val pol2 = map f mfl
      val pol3 = normalize_distrib pol2
      val pol4 = if !game.noise_flag then add_noise pol3 else pol3
    in
      pol4
    end
  else
    let  
      val f = fp_emb_either
      val progle = if null boarde then f stack_empty [] else #4 (hd boarde)
      val preboarde = 
         if !notarget_flag then progle else
         f pair_progseq [progle,targete]
      val prepolie = f prepoli [preboarde]
      val ende = f head_poli [prepolie]
      val pol1 = Vector.fromList (mlNeuralNetwork.descale_out ende)
      val pol2 = map (fn x => (x, Vector.sub (pol1, fst x))) mfl
      val pol3 = normalize_distrib pol2
      val pol4 = if !game.noise_flag then add_noise pol3 else pol3
    in
      pol4
    end

(* -------------------------------------------------------------------------
   Search limited by number of visits or a timeout
   ------------------------------------------------------------------------- *)
 
val search_time_flag = ref false

fun search_move_vis rt depth targete boarde ((move,f),vis) =
  if vis <= 0 then () else
  search_aux rt depth (vis,(0.0,0.0)) targete (apply_move (move,f) boarde)

and search_move_tim rt depth targete boarde ((move,f),(torg,tinc)) =
  if torg + tinc <= Time.toReal (Timer.checkRealTimer rt) then () else
  search_aux rt depth (0,(torg,tinc)) targete (apply_move (move,f) boarde)

and search_move rt depth (vis,tim) targete boarde pol =
  if !search_time_flag 
  then 
    app (search_move_tim rt depth targete boarde) (split_tim tim pol)
  else 
    if vis - 1 <= 0 then () else
    app (search_move_vis rt depth targete boarde) (split_vis (vis - 1) pol)

and search_aux rt depth (vis,tim) targete boarde = 
  if depth >= 10000 then () else
  let  
    val (newboarde, mfl) = collect_children boarde 
      handle NotFound => raise ERR "collect_children" ""         
    val pol = create_pol targete newboarde mfl
  in
    search_move rt (depth + 1) (vis,tim) targete newboarde pol
  end

fun search (vis,tinc) = 
  let 
    val _ = search_time_flag := (vis <= 0)
    val _ = node_counter := 0  
    val _ = prog_counter := 0
    val _ = checkinit ()
    val targete = get_targete ()
    val rt = Timer.startRealTimer ()
    val (_,t) = add_time (search_aux rt 0 (vis,(0.0,tinc)) targete) []
  in
    print_endline ("nodes: " ^ its (!node_counter));
    print_endline ("programs: " ^ its (!prog_counter));
    print_endline ("search time: "  ^ rts_round 2 t ^ " seconds")
  end
  
(* -------------------------------------------------------------------------
   Search using the RNN
   ------------------------------------------------------------------------- *)
  
val search_time_flag = ref false

fun search_move_vis rt depth targete boarde ((move,f),vis) =
  if vis <= 0 then () else
  search_aux rt depth (vis,(0.0,0.0)) targete (apply_move (move,f) boarde)

and search_move_tim rt depth targete boarde ((move,f),(torg,tinc)) =
  if torg + tinc <= Time.toReal (Timer.checkRealTimer rt) then () else
  search_aux rt depth (0,(torg,tinc)) targete (apply_move (move,f) boarde)

and search_move rt depth (vis,tim) targete boarde pol =
  if !search_time_flag 
  then 
    app (search_move_tim rt depth targete boarde) (split_tim tim pol)
  else 
    if vis - 1 <= 0 then () else
    app (search_move_vis rt depth targete boarde) (split_vis (vis - 1) pol)

and search_aux rt depth (vis,tim) targete boarde = 
  if depth >= 10000 then () else
  let  
    val (newboarde, mfl) = collect_children boarde 
      handle NotFound => raise ERR "collect_children" ""         
    val pol = create_pol targete newboarde mfl
  in
    search_move rt (depth + 1) (vis,tim) targete newboarde pol
  end

fun search_rnn (vis,tinc) = 
  let 
    val _ = search_time_flag := (vis <= 0)
    val _ = node_counter := 0  
    val _ = prog_counter := 0
    val _ = checkinit ()
    val targete = tokenize_seq (!target_glob)
    val rt = Timer.startRealTimer ()
    val (_,t) = add_time (search_aux rt 0 (vis,(0.0,tinc)) targete) []
  in
    print_endline ("nodes: " ^ its (!node_counter));
    print_endline ("programs: " ^ its (!prog_counter));
    print_endline ("search time: "  ^ rts_round 2 t ^ " seconds")
  end  
  
  
(* -------------------------------------------------------------------------
   Search starting from a particular goal (use in cube)
   ------------------------------------------------------------------------- *) 
 
fun get_boarde board =
  let 
    val bmltop = game.linearize_board board
    fun f bml boarde = case bml of [] => boarde | (_,move) :: m =>
      let 
        val (_,exec) = valOf (collect_child boarde move)
        val newboarde = apply_move (move,exec) boarde
      in
        f m newboarde
      end
    val r = f bmltop [] 
    val _ = if #board_compare (game.game) (map #1 r, board) <> EQUAL 
            then raise ERR "get_boarde" ""
            else ()
  in
    r
  end

fun search_board (vis,tinc) board =
  let 
    val _ = search_time_flag := (vis <= 0)
    val _ = prog_counter := 0
    val _ = node_counter := 0  
    val targete = get_targete ()
    val boarde = get_boarde board
    val rt = Timer.startRealTimer ()
    val (_,t) = add_time (search_aux rt 0 (vis,(0.0,tinc)) targete) boarde
  in
    print_endline ("nodes: " ^ its (!node_counter));
    print_endline ("programs: " ^ its (!prog_counter));
    print_endline ("search time: "  ^ rts_round 2 t ^ " seconds")
  end


(* -------------------------------------------------------------------------
   Beam search
   ------------------------------------------------------------------------- *) 
 
val progd = ref (eempty prog_compare)

fun exec_fun move l1 l2 =
  let 
    val f = fp_emb_either
    val p = (Ins (move, map #1 (rev l1)))
    val _ = progd := eadd p (!progd)
  in
    if !randsearch_flag orelse !simple_flag then (p,empty_emb,empty_emb) :: l2 else
    let
      val oper = Vector.sub (operv,move)
      val emb1 = 
        if arity_of oper <= 0 
        then f oper []
        else f (cap_tm oper) [f oper (map #2 (rev l1))]
      val emb2 = 
        if null l2 then emb1 else
        f (cap_tm stack_cat) [f stack_cat [emb1, #3 (hd l2)]]
    in
      ((p,emb1,emb2) :: l2)
    end
  end

fun apply_move move boarde =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity boarde
  in
    if length l1 <> arity 
    then raise ERR "apply_move" ""
    else (exec_fun move l1 l2)
  end
  
fun create_pol targete boarde ml =
  if !randsearch_flag 
    then normalize_distrib (map (fn x => (x, random_real ())) ml)
  else
  let  
    val f = fp_emb_either
    val progle = if null boarde then f stack_empty [] else #3 (hd boarde)
    val preboarde = 
       if !notarget_flag then progle else
       f pair_progseq [progle,targete]
    val prepolie = f prepoli [preboarde]
    val ende = f head_poli [prepolie]
    val pol1 = Vector.fromList (mlNeuralNetwork.descale_out ende)
    val pol2 = map (fn x => (x, Vector.sub (pol1,x))) 
      (if !stop_flag then maxmove :: ml else ml)
    val pol3 = normalize_distrib pol2
    val pol4 = if !game.noise_flag then add_noise pol3 else pol3
  in
    pol4
  end
  
fun beamsearch_aux targete maxwidth maxdepth depth beaml =
  if depth >= maxdepth orelse maxwidth <= 0 then () else  
  let 
    fun f (boarde,sc) =
      let 
        val ml = available_movel boarde 
        val pol = create_pol targete boarde ml
        fun g (m,msc) = ((boarde,m),sc * msc)
      in
        map g pol
      end 
    val beaml1 = dict_sort compare_rmax (List.concat (map f beaml))
    val beaml2 = first_n maxwidth beaml1
    val i = ref 0
    fun h ((boarde,m),sc) = 
      if !stop_flag andalso m = maxmove 
      then (incr i; NONE) 
      else SOME (apply_move m boarde, sc)
    val beaml3 = List.mapPartial h beaml2
  in
    beamsearch_aux targete (maxwidth - !i) maxdepth (depth + 1) beaml3
  end

fun beamsearch () =  
  let 
    val _ = progd := eempty prog_compare
    fun f () =
      let 
        val _ = select_random_target ()
        val targete = get_targete ()
      in
        beamsearch_aux targete 1000 240 0 [([],1.0)]
      end
    fun loop n = if n <= 0 then () else (f (); loop (n-1))
    val (_,t) = add_time loop 1
    val _ = print_endline 
      ("beamsearch: " ^ its (elength (!progd)) ^ " " ^ rts_round 2 t)
    val (sol,t) = add_time checkpl (elist (!progd))
    val _ = print_endline 
      ("checkpl: " ^ its (length sol) ^ " " ^ rts_round 2 t)
  in
    sol
  end
 
end (* struct *)

(* 
PolyML.print_depth 3;
load "search"; open kernel aiLib search;
tnn.update_fp_op (selfdir ^ "/tnn_in_c/ob_online.so");
bloom.select_random_target ();
randsearch_flag := false;
val sol = beamsearch ();

check.checkinit ();
search (0, 60.0);
val _ = check.checkfinal ();

(*
solutions: 3373
checkb: 5381
checkb time: 93.18 seconds
more solutions: 3689
> val it = 55: int
*)



*)
