structure search :> search =
struct

open HolKernel boolLib aiLib kernel bloom mlTreeNeuralNetwork tnn exec check bloom
val ERR = mk_HOL_ERR "search"
type emb = real vector

(* first embedding is prog embedding, second is stack *)
type boarde = (kernel.prog * exec.exec * emb * emb) list
val randsearch_flag = ref false

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

val movelg = filter (fn x => not (String.isPrefix "runz" (name_of_oper x)))
   (List.tabulate (Vector.length operv, I))

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
    if !randsearch_flag then (p,exec,empty_emb,empty_emb) :: l2 else
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

val runoffset = oper_of_name "runz0" handle HOL_ERR _ => 0

val natbase = IntInf.fromInt 10
val azero = IntInf.fromInt 0

fun movel_of_execr r =
  if r < azero then 10 :: movel_of_execr (~r) else
  if r < natbase then [IntInf.toInt r]
  else IntInf.toInt (r mod natbase) :: movel_of_execr (r div natbase)

fun expand_run (move,exec) boarde =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity boarde
    val p = (Ins (move, map #1 (rev l1))) 
    val pexec = exec_intl.mk_exec p
    val _ = init_timer ()
    val r = hd (pexec ([azero], [azero])) 
      handle _ => IntInf.fromInt 1000000
    val ml =    
      if r > IntInf.fromInt 999999 then []
      else if r < IntInf.fromInt (~999999) then []
      else movel_of_execr r
  in
    (move,exec) :: map (fn x => (x + runoffset, (fn (a,b,c) => a))) ml
  end

fun apply_move_one ((move,exec),boarde) =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity boarde
  in
    if length l1 <> arity 
    then raise ERR "apply_move" (name_of_oper move)
    else exec_fun (move,exec) l1 l2
  end
   
fun apply_movel movele boarde = foldl apply_move_one boarde movele

fun apply_move (move,exec) boarde =
  if !intl_flag andalso name_of_oper move = "run"
  then apply_movel (expand_run (move,exec) boarde) boarde
  else apply_move_one ((move,exec),boarde)

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
      val exec = 
        if !intl_flag orelse !memo_flag orelse !ctree_flag
        then (fn (a,b,c) => a) 
        else mk_exec_move move (map #2 (rev l1))  
    in 
      if !locsearch_flag andalso null l2 andalso not (depend_on_y p)
      then (incr prog_counter; 
            checkonline 0.0 (p,exec); 
            SOME (move, cache_exec exec))
      else SOME (move,exec)
    end
  end

fun collect_children nnvalue boarde = case boarde of
    [(p,exec,a,b)] =>
    let 
      val _ = if not (!locsearch_flag) 
              then (
                   incr prog_counter;
                   if !ramsey_flag then
                     checkonline_ramsey (p,exec)
                   else if !pgen_flag 
                   then checkonline_pgen (p,exec)
                   else checkonline nnvalue (p,exec)
                   )
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

fun add_temp l = 
  if Real.compare (temperature,1.0) = EQUAL then l else
  map_snd (fn x => Math.pow (x, 1.0 / temperature)) l


fun create_pol targete boarde mfl =
  if !randsearch_flag 
    then normalize_distrib (map (fn x => (x, random_real ())) mfl)
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
      val pol3 = normalize_distrib (add_temp pol2)
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
  then app (search_move_tim rt depth targete boarde) (split_tim tim pol)
  else 
    if vis - 1 <= 0 then () else
    app (search_move_vis rt depth targete boarde) (split_vis (vis - 1) pol)

and search_aux rt depth (vis,tim) targete boarde = 
  if depth >= maxproglen then () else
  let
    val (newboarde, mfl) = collect_children (snd tim) boarde       
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
val onlystop = ref false

fun exec_fun move l1 l2 =
  let 
    val f = fp_emb_either
    val p = (Ins (move, map #1 (rev l1)))
    val _ = if !onlystop then () else progd := eadd p (!progd)
  in
    if !randsearch_flag then (p,empty_emb,empty_emb) :: l2 else
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
    then normalize_distrib (map (fn x => (x, random_real ())) 
      (if !stop_flag then maxmove :: ml else ml))
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
        beamsearch_aux targete beam_width maxproglen 0 [([],1.0)]
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
  
(* -------------------------------------------------------------------------
   Alternative beam search 1: ordered and without subprograms
   and only allow stopping when the board is a singleton
   acceptable board avoids too many duplicate sequences  
   (especially at the start of the run)
   Does not work with a random network (use MCTS instead)
   ------------------------------------------------------------------------- *)  
  
val seqd = ref (dempty seq_compare)  

fun clip_seq seq =  
  let
    val minint = IntInf.fromInt (valOf Int.minInt)
    val maxint = IntInf.fromInt (valOf Int.maxInt)
    fun f x = if x < minint then minint
              else if x > maxint then maxint
              else x
  in
    map f seq
  end

fun acceptable_boarde boarde = 
  if not (is_singleton boarde) then false else
  let 
    val prog = #1 (hd boarde) 
    val seq = clip_seq (exec_memo.penum_wtime short_timeincr prog 16)
  in
    not (length seq < 16) andalso not (dmem seq (!seqd))
  end

fun beamsearch_ordered_aux targete maxwidth maxdepth depth beaml =
  if depth >= maxdepth orelse dlength (!seqd) >= maxwidth then () else
  let 
    fun f (boarde,sc) =
      let 
        val ml = available_movel boarde 
        val pol = create_pol targete boarde ml
        fun g (m,msc) = 
          if m = maxmove andalso not (acceptable_boarde boarde)
          then NONE
          else SOME ((boarde,m),sc * msc)
      in
        List.mapPartial g pol
      end 
    val beaml1 = dict_sort compare_rmax (List.concat (map f beaml))
    val beaml2 = first_n (maxwidth - (dlength (!seqd))) beaml1
    fun h ((boarde,m),sc) =
      if !stop_flag andalso m = maxmove 
      then 
         let 
           val prog = #1 (hd boarde) 
           (* inefficient as already computed before *)
           val seq = clip_seq (exec_memo.penum_wtime short_timeincr prog 16)
         in
           seqd := dadd seq (prog,sc) (!seqd); 
           NONE
         end
      else SOME (apply_move m boarde, sc)
    val beaml3 = List.mapPartial h beaml2
  in
    beamsearch_ordered_aux targete maxwidth maxdepth (depth + 1) beaml3
  end

fun beamsearch_ordered width target =  
  let 
    val _ = seqd := dempty seq_compare
    fun f () =
      let 
        val _ = target_glob := target
        val targete = get_targete ()
      in
        beamsearch_ordered_aux targete width maxproglen 0 [([],1.0)]
      end
    fun loop n = if n <= 0 then () else (f (); loop (n-1))
    val (_,t) = add_time loop 1
    val _ = print_endline ("beamsearch: " ^ 
      its (dlength (!seqd)) ^ " sequences in " ^ rts_round 2 t ^ " seconds")
  in
    dict_sort (snd_compare compare_rmax) (dlist (!seqd))
  end
  
(* 
PolyML.print_depth 0;
load "search"; open kernel aiLib search bloom;
PolyML.print_depth 10;
val (an,seq) = bloom.select_random_target2 ();
search.randsearch_flag := true;
val progsc = beamsearch_ordered 1000 seq;
PolyML.print_depth 40;
fun f (seq,(p,sc)) = (seq,(human.humanf p, sc));
val l = map f progsc;

(*
val (sol,t) = add_time checkpl (dkeys (!seqd))
val _ = print_endline 
("checkpl: " ^ its (length sol) ^ " " ^ rts_round 2 t)
*)
*)  
(* -------------------------------------------------------------------------
   Alternative beam search 2: ordered and without subprograms
   and only allow stopping when the board is a singleton
   acceptable board avoids too many duplicate sequences  
   (especially at the start of the run)
   Does not work with a random network (use MCTS instead)
   ------------------------------------------------------------------------- *)  

fun beamsearch_target_aux pd targete maxwidth maxdepth depth beaml =
  if depth >= maxdepth orelse dlength (!pd) >= maxwidth then () else
  let 
    fun f (boarde,sc) =
      let 
        val ml = available_movel boarde 
        val pol = create_pol targete boarde ml
        fun g (m,msc) = 
          if m = maxmove andalso not (is_singleton boarde)
          then NONE
          else SOME ((boarde,m),sc * msc)
      in
        List.mapPartial g pol
      end 
    val beaml1 = dict_sort compare_rmax (List.concat (map f beaml))
    val beaml2 = first_n (maxwidth - (dlength (!pd))) beaml1
    fun h ((boarde,m),sc) =
      if !stop_flag andalso m = maxmove 
      then (pd := dadd (#1 (hd boarde)) sc (!pd); NONE)
      else SOME (apply_move m boarde, sc)
    val beaml3 = List.mapPartial h beaml2
  in
    beamsearch_target_aux pd targete maxwidth maxdepth (depth + 1) beaml3
  end

fun beamsearch_target width target =  
  let 
    val pd = ref (dempty prog_compare)
    fun f () =
      let 
        val _ = target_glob := target
        val targete = get_targete ()
      in
        beamsearch_target_aux pd targete width maxproglen 0 [([],1.0)]
      end
    fun loop n = if n <= 0 then () else (f (); loop (n-1))
    val (_,t) = add_time loop 1
    val _ = print_endline ("beamsearch: " ^ 
      its (dlength (!pd)) ^ " sequences in " ^ rts_round 2 t ^ " seconds")
  in
    dict_sort compare_rmax (dlist (!pd))
  end
 
(* -------------------------------------------------------------------------
   Search with self-selected training set
   ------------------------------------------------------------------------- *)
 
fun loop_smartselect tim =
  if dlength (!check.seqd) >= 1024 then
    let 
      val e1 = dlist (!check.seqd)
      val e2 = dict_sort 
        (snd_compare (cpl_compare Int.compare prog_compare_size)) e1
    in
      map (fn (a,(b,c)) => (a,c)) (first_n 1024 e2)
    end
  else (ignore (search (0,tim)); loop_smartselect (2.0*tim));


(* copied from rl *)
fun expdir () = selfdir ^ "/exp/" ^ !expname
fun histdir () = expdir () ^ "/hist"
fun exdir () = expdir () ^ "/ex"
fun is_number s = all Char.isDigit (explode s)

fun find_last s =
  let 
    val sl1 = listDir (histdir ())
    val sl2 = filter (String.isPrefix s) sl1
    val sl3 = mapfilter (snd o split_string s) sl2
    val sl4 = filter is_number sl3
    val il = mapfilter string_to_int sl4
  in
    if null il 
    then raise ERR "find_last" ("no " ^ s)
    else list_imax il
  end

fun itsol_file ngen = histdir () ^ "/itsol" ^ its ngen
fun read_last_itsol () = read_itprogl (itsol_file (find_last "itsol"))

(* end copy *)

fun search_smartselect dir =
  let
    val exdirloc = exdir ()
    val _ = clean_dir dir
    val tnndir = selfdir ^ "/tnn_in_c"
    val datadir = dir ^ "/data"
    val _ = app mkDir_err [dir,datadir]
    (* *)
    val itsol = read_last_itsol () handle HOL_ERR _ => []
    fun f x = (string_to_int o snd o split_string "exA") x
    val d = enew Int.compare (map f (listDir exdirloc))
    val itsolsmall = filter (fn (a,b) => not (emem a d)) itsol
    val _ = 
      if random_real () > 0.5 orelse length itsolsmall < 100
      then bloom.select_random_target_avoiding d
      else 
        let 
          val targetn = random_elem (map fst itsolsmall)
          val target = valOf (Array.sub (oseq, targetn))
        in
          targetn_glob := targetn; target_glob := target
        end
    (* randomly generated training examples *)
    val _ = check.seqd := aiLib.dempty kernel.seq_compare
    val _ = randsearch_flag := true
    val _ = kernel.nooeis_flag := true
    val ex1 = loop_smartselect 60.0
    val ex2 = random_subset 256 ex1    
    val nex = length ex2
    val _ = print_endline (its nex ^ " examples generated")
    (* randomly generated training examples end *)
    val ex3 = create_exl_seqprogl (shuffle ex2)
    val _ = randsearch_flag := false;
    val _ = kernel.nooeis_flag := false;
    val nex = length ex3
    val _ = export_traindata datadir 100 0.001 96 ex3
    val _ = print_endline (its nex ^ " examples exported: " ^ datadir)
    val _ = cmd_in_dir tnndir ("cp tree " ^ dir)
    val logfile = dir ^ "/log"
    val (_,t) = add_time (cmd_in_dir dir) ("./tree" ^ " > " ^ logfile)
    val _ = print_endline ("train time: " ^ rts_round 4 t)
    val obfile = dir ^ "/ob.c"
    val obfst = tnndir ^ "/ob_fst.c"
    val obsnd = tnndir ^ "/ob_snd.c"
    val catcmd = String.concatWith " " ["cat",obfst,"out_ob",obsnd,">",obfile]
    val () = cmd_in_dir dir catcmd
    val () = cmd_in_dir tnndir ("sh compile_ob.sh " ^ obfile)
    val fileso = dir ^ "/ob.so"
    val () = update_fp_op fileso 96;
    val (pscl,t) = add_time (beamsearch_target 10000) (!target_glob)
    val _ = print_endline ("beam time: " ^ rts_round 4 t)
    val ((rank,itsol),t) = add_time (check.checkpl_target (!targetn_glob)) 
      (map fst pscl)
    val _ = print_endline ("check time: " ^ rts_round 4 t)
    val exAfile = dir ^ "/exA" ^ its (!targetn_glob)
  in
    if rank < 0 then () else write_seqprog exAfile ex2;
    itsol
  end 
 
 
end (* struct *)

(* 
PolyML.print_depth 0;
load "search"; open kernel aiLib search bloom;
PolyML.print_depth 10;
val (an,seq) = bloom.select_random_target2 ();
search.randsearch_flag := true;
val pl = beamsearch_target 10000 seq;
val (rank,itsol) = check.checkpl_target 27 (map fst pl);

*)
(*
PolyML.print_depth 10;
load "search"; open kernel aiLib search bloom;
tnn.update_fp_op (selfdir ^ "/model/ob_online.so");
check.checkinit ();
search (0, 60.0);
val _ = check.checkfinal ();
*)
