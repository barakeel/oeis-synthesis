structure search :> search =
struct

open HolKernel boolLib aiLib kernel bloom mlTreeNeuralNetwork tnn 
  exec check bloom
val ERR = mk_HOL_ERR "search"
type emb = real vector

val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)

(* first embedding is prog embedding, second is stack *)
type boarde = (kernel.prog * exec.exec * emb * emb) list
val randsearch_flag = ref false
val rand_exp = ref 1.0

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
  apply_move_one ((move,exec),boarde)

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
      val exec = (fn (a,b,c) => a)
    in 
      SOME (move,exec)
    end
  end

fun collect_children nnvalue boarde = case boarde of
    [(p,exec,a,b)] =>
    let 
      val _ = (incr prog_counter; checkonline nnvalue (p,exec))
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
    then 
      let fun f x = if Real.compare (!rand_exp,1.0) <> EQUAL 
                    then (x, Math.pow (random_real (), !rand_exp))
                    else (x, random_real ())
      in
        normalize_distrib (map f mfl)
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
    val _ = if !ngen_glob <= 0 then timeincr := init_timeincr else ()
    val _ = node_counter := 0  
    val _ = prog_counter := 0
    val _ = checkinit ()
    val targete = 
      if !randsearch_flag then Vector.fromList [100.0] else get_targete ()
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

fun apply_move1 move board =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board
  in
    if length l1 <> arity 
    then raise ERR "apply_move" ""
    else (Ins (move, rev l1))
  end

fun exec_fun move l1 l2 =
  let 
    val f = fp_emb_either
    val p = (Ins (move, map #1 (rev l1)))
    val _ = if !onlystop then () else      
      if !locsearch_flag 
      then 
        let 
          val boarde = l1 @ l2
          val board = map #1 boarde
          val ml = available_movel boarde
          fun f m = 
            let val ploc = apply_move1 move board in
              progd := eadd ploc (!progd)
            end
        in
          app f ml
        end
      else progd := eadd p (!progd)
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
 
fun gen_random_ex_aux tim =
  if dlength (!check.seqd) >= 1024 then
    let 
      val e1 = dlist (!check.seqd)
      val e2 = dict_sort 
        (snd_compare (cpl_compare Int.compare prog_compare_size)) e1
    in
      map (fn (a,(b,c)) => (a,c)) (first_n 1024 e2)
    end
  else (ignore (search (0,tim)); gen_random_ex_aux (2.0*tim));

fun gen_random_ex () =
  let
    val _ = check.seqd := dempty seq_compare
    val _ = kernel.nooeis_flag := true
    val ex1 = gen_random_ex_aux 60.0
    val _ = kernel.nooeis_flag := false
    val ex2 = random_subset 256 ex1    
  in
    ex2
  end
  
fun gen_ex target = 
  map (fn (a,(b,c)) => (a,b)) (beamsearch_ordered 256 target)
 
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
    (* select a random target not too randomly *)
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
    val ex2 = if !randsearch_flag 
              then gen_random_ex () 
              else gen_ex (!target_glob)
    val ex3 = create_exl_seqprogl (shuffle ex2)
    val nex = length ex3
    val _ = print_endline (its nex ^ " examples generated")
    (* exporting data *)
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
    val memf = !fp_op_glob
    val mem = !randsearch_flag
    val () = update_fp_op fileso 96
    val _ = randsearch_flag := false
    val (pscl,t) = add_time (beamsearch_target 10000) (!target_glob)
    val _ = fp_op_glob := memf
    val _ = randsearch_flag := mem
    val _ = print_endline ("beam time: " ^ rts_round 4 t)
    val ((rank,itsol),t) = add_time (check.checkpl_target (!targetn_glob)) 
      (map fst pscl)
    val _ = print_endline ("check time: " ^ rts_round 4 t)
    val exAfile = dir ^ "/exA" ^ its (!targetn_glob)
  in
    if rank < 0 then () else write_seqprog exAfile ex2;
    itsol
  end 
 
(* -------------------------------------------------------------------------
   Generate programs with program generator
   ------------------------------------------------------------------------- *)

fun init_timer_wtim tim = 
  (push_counter := 0; abstimer := 0; timelimit := tim);

val prnn_counter = ref 0

exception Break;

local open exec_prnn in

fun beamsearch_prnn_one tim lim p seq (tokenl,embv) = 
  if !prnn_counter >= lim then raise Break else 
  let 
    val _ = seq_glob := seq
    val _ = seqlen_glob := IntInf.fromInt (length (!seq_glob))
    val _ = prog_glob := tokenl
    val _ = proglen_glob := IntInf.fromInt (length (!prog_glob))
    val _ = embv_glob := embv
    val _ = emblen_glob := IntInf.fromInt (Vector.length (!embv_glob))
    val exec = mk_exec p
    val _ = init_timer_wtim tim
    val newembl = List.tabulate (16,fn i => (i, exec ([IntInf.fromInt i],[0])))
    fun f (i,x) = if hd x > 0 then SOME i else NONE
    val nextl = List.mapPartial f newembl
    val newembv = Vector.fromList (map snd newembl)
  in
    SOME (map (fn x => (incr prnn_counter; 
      (IntInf.fromInt x :: tokenl,newembv))) nextl)
  end
  handle 
       Empty => NONE
     | Div => NONE
     | ProgTimeout => NONE
     | Overflow => NONE
     | Subscript => NONE
  ; 
 
end (* local *)
 
fun distrib_token (tokenl,(stopb,(nexttokenl,newembv))) =
  map (fn x => (x :: tokenl,newembv)) nexttokenl;
     
fun beamsearch_prnn_loop i pd p seq tim lim tokembl =
  let 
    val _ = prnn_counter := 0
    val l1 = (List.concat 
      (List.mapPartial (beamsearch_prnn_one tim lim p seq) tokembl))
      handle Break => []
    val (compl,contl) = partition (isSome o prog_of_movelo o 
      map IntInf.toInt o fst) l1
    val progl = List.mapPartial prog_of_movelo 
      (map (map IntInf.toInt o fst) compl)
    val newpd = eaddl progl pd
  in
    if elength newpd > lim then pd else
    if null contl orelse  i > maxproglen then newpd 
    else beamsearch_prnn_loop (i+1) newpd p seq tim lim contl
  end

fun beamsearch_prnn p seq tim lim =
  let 
    val tokembl = [([]: IntInf.int list,
      (Vector.tabulate (16, fn _ => [IntInf.fromInt 0])))]
    val pd = eempty prog_compare
  in
    beamsearch_prnn_loop 0 pd p seq tim lim tokembl
  end

fun gen_prog anuml pid p =
  let
    fun f anum =
      let 
        val seq = valOf (Array.sub (bloom.oseq,anum))
        val pl = elist (beamsearch_prnn p seq 100000 10000)
        fun g p = case dfindo p (!pid) of SOME i => i | NONE =>
          let val i = dlength (!pid) in
            pid := dadd p i (!pid); i   
          end
        val il = map g pl     
      in
        (anum,il)
      end
  in
    map f anuml
  end
  
fun gen_progl anuml pl = 
  let 
    val pid = ref (dempty prog_compare) 
    val rl = map_assoc (gen_prog anuml pid) pl
  in
    (rl,!pid)
  end


fun filter_unique_prog_one pset rl counter (pg,anum) =
  let 
    val _ = 
      if counter <> 0 andalso counter mod 100000 = 0 
      then print_endline (its counter ^ ": " ^ 
        "generators " ^ its (length (!rl)) ^ ", " ^ 
        "programs " ^ its (elength (!pset)))
      else ()
    val seq = valOf (Array.sub (bloom.oseq,anum))
    val pl = elist (beamsearch_prnn pg seq 100000 10000)
    fun g p = 
      if emem p (!pset) 
      then false
      else (pset := eadd p (!pset); true)
    val bl = map g pl   
  in
    if exists I bl 
    then rl := pg :: !rl
    else ()
  end


fun extend_anuml anuml ntop n =
  if n <= ntop
  then random_subset n (shuffle anuml) 
  else (shuffle anuml) @ extend_anuml anuml ntop (n - ntop)

fun filter_unique_prog pl = 
  let
    val anuml = map fst oseql
    val anumle = extend_anuml anuml (length anuml) (length pl)
    val panuml = combine (pl,anumle)
    val rl = ref []
    val pset = ref (eempty prog_compare)
  in
    appi (filter_unique_prog_one pset rl) panuml;
    rev (!rl)
  end


fun filter_unique_fun_one pset rl counter (pg,anum) =
  let
    val seq = valOf (Array.sub (bloom.oseq,anum))
    val pl = elist (beamsearch_prnn pg seq 100000 10000)
    fun g p =
      if emem p (!pset) 
      then NONE
      else (pset := eadd p (!pset); SOME p)
    val pl' = List.mapPartial g pl   
  in
    if null pl' then () else rl := (pg,pl') :: !rl
  end

fun random_pgenl n timtop =
  let 
    val _ = randsearch_flag := true
    val _ = rand_exp := 5.0
    fun loop tim =
      let 
        val _ = check.prnnd := dempty prog_compare
        val _ = search (0,tim) 
      in
        if dlength (!check.prnnd) >= n 
        then map fst 
          (first_n n (dict_sort compare_rmax (dlist (!check.prnnd))))
        else loop (tim * 2.0)
      end
    val pgenl = loop timtop
    val _ = randsearch_flag := false
    val _ = rand_exp := 1.0
  in
    pgenl
  end

fun infer_pgenl fileso n timtop =
  let
    val _ = update_fp_op fileso dim_glob
    fun loop tim =
      let 
        val _ = check.prnnd := dempty prog_compare
        val _ = search (0,tim) 
      in
        if dlength (!check.prnnd) >= n 
        then map fst 
          (first_n n (dict_sort compare_rmax (dlist (!check.prnnd))))
        else loop (tim * 2.0)
      end
    val pgenl = loop timtop
  in
    pgenl
  end


fun filter_unique_fun () () = 
  let
    val pl = random_pgenl (int_pow 10 6) 32.0
    val anuml = map fst oseql
    val anumle = extend_anuml anuml (length anuml) (length pl)
    val panuml = combine (pl,anumle)
    val rl = ref []
    val pset = ref (eempty prog_compare)
  in
    appi (filter_unique_fun_one pset rl) panuml;
    print_endline 
      ("generators " ^ its (length (!rl)) ^ ", " ^ 
       "programs " ^ its (elength (!pset)));
    rev (!rl)
  end



fun write_unit (file:string) () = ()
fun read_unit (file:string) = ()

fun string_of_ppl (p,pl) = 
  String.concatWith "," (map gpt_of_prog (p :: pl))

fun write_ppll file ppll = 
  writel file (map string_of_ppl ppll)
  
fun ppl_of_string s = 
  let val sl = String.tokens (fn x => x = #",") s in
    (prog_of_gpt (hd sl), map prog_of_gpt (tl sl))
  end 

fun read_ppll file = 
  map ppl_of_string (readl file)

val filteruniquespec : 
  (unit, unit, (prog * prog list) list) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "search.filteruniquespec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = filter_unique_fun,
  write_param = write_unit,
  read_param = read_unit,
  write_arg = write_unit,
  read_arg = read_unit,
  write_result = write_ppll,
  read_result = read_ppll
  }

fun interleave ll = case ll of 
    [] => []
  | _ => mapfilter hd ll @ interleave (mapfilter tl ll)
  
fun merge_filterunique dir pplll =
  let 
    val ppll = interleave pplll
    val pset = ref (eempty prog_compare)
    val rl = ref []
    fun g p = 
      if emem p (!pset) 
      then false
      else (pset := eadd p (!pset); true)
    fun f (pg,pl) =
      let val bl = map g pl in
        if exists I bl 
        then rl := pg :: !rl
        else ()
      end
  in
    app f ppll; 
    print_endline ("generators " ^ its (length (!rl)) ^ ", " ^ 
                   "programs " ^ its (elength (!pset)));
    append_file (dir ^ "/log") 
       ("generators " ^ its (length (!rl)) ^ ", " ^ 
        "programs " ^ its (elength (!pset)));
    rev (!rl)
  end     
        
fun parallel_filterunique n =
  let  
    val dir = selfdir ^ "/filterunique"
    val _ = clean_dir dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 10000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val param = ()
    val argl = List.tabulate (n, fn _ => ())
    val (pplll,t) = add_time 
      (smlParallel.parmap_queue_extern ncore filteruniquespec param) argl
    val _ = writel (dir ^ "/log") ["parallel time: " ^ rts_round 4 t]
    val pl = merge_filterunique dir pplll
  in
    write_progl (dir ^ "/pgen") pl;
    pl
  end


(* 
PolyML.print_depth 0;
load "search"; open aiLib kernel bloom search;
PolyML.print_depth 10;
val pl1 = random_pgenl (int_pow 10 6) 32.0;
val pl1b = random_pgenl (int_pow 10 6) 32.0;
val pl1c = random_pgenl (int_pow 10 6) 32.0;
val pltot = mk_fast_set prog_compare (pl1 @ pl1b @ pl1c);
length pltot;

val (pl2,t) = add_time filter_unique_prog pl1;
app (print_endline o human.humanf) pl2;

val pl = parallel_filterunique 1000;
length pl

*)

(*
PolyML.print_depth 0;
load "search"; open aiLib kernel bloom search;
PolyML.print_depth 10;
val pl = parallel_filterunique 1000;
*)

(* -------------------------------------------------------------------------
   Prepare a curriculum
   ------------------------------------------------------------------------- *)

(*
val itsol843 = read_itprogl "model/itsol843";

fun is_smaller (t1,p1) (t2,p2) = 
  triple_compare Int.compare Int.compare prog_compare 
      ((prog_size p1,t1,p1),(prog_size p2,t2,p2)) = LESS;

val ERR = mk_HOL_ERR "test";
fun smallest tpl = case tpl of 
    [a] => snd a
  | [a,b] => if is_smaller a b then snd a else snd b
  | _ => raise ERR "smallest" "";

val itsol843small = map_snd smallest itsol843;
val itsol843size = dict_sort compare_imin (map_snd prog_size itsol843small);   

write_anumprog "data/oeis_smallprog" itsol843small;
writel "data/oeis_order" (map (its o fst) (itsol843size));
*)

(* assumes ordered list without repetition *)
fun list_diff_ordered l1 l2 = case (l1,l2) of
    ([],x) => []
  | (x,[]) => x
  | (a1 :: m1, a2 :: m2) => 
    (
    case Int.compare (a1,a2) of
       EQUAL => list_diff_ordered m1 m2 
     | LESS => a1 :: list_diff_ordered m1 l2
     | GREATER => list_diff_ordered l1 m2
    )

fun create_round_aux n seln easyl hardd acc = 
  if n <= 0 then rev acc else
  let 
    val (easylsel,easyl1) = part_n seln easyl
    val hardd1 = ereml easylsel hardd
    val hardlsel = random_subset seln (elist hardd1)
    val easyl2 = list_diff_ordered easyl1 (elist (enew Int.compare hardlsel))
    val hardd2 = ereml hardlsel hardd1 
  in
    create_round_aux (n-1) (2*seln) easyl2 hardd2 
      ((easylsel @ hardlsel) :: acc)
  end;

fun create_round n seln easyl hardl =
  create_round_aux n seln easyl (enew Int.compare hardl) []

(* -------------------------------------------------------------------------
   Collect and evaluate generated programs
   ------------------------------------------------------------------------- *)

fun collect_prog genl = 
  let fun f (_,apll) = List.concat (map snd apll) in
    List.concat (map f genl)
  end  
  
fun eval_prog p = map fst (exec_prnn.coverf_oeis (exec_prnn.mk_exec p))

(* -------------------------------------------------------------------------
   Replace generated programs by the OEIS sequence they generate
   ------------------------------------------------------------------------- *)

val ibcmp = cpl_compare Int.compare bool_compare;

fun expand_ipl evald (anum,pl) = 
  let 
    val l1 = List.concat (map (fn x => dfind x evald) pl) 
    fun f a = if a = anum then [(a,false),(a,true)] else [(a,false)]
    val l2 = map f l1 
  in
    List.concat l2
  end

fun expand_ipll evald ipll = 
  mk_fast_set ibcmp (List.concat (map (expand_ipl evald) ipll))

(* -------------------------------------------------------------------------
   Find closest neighbor
   ------------------------------------------------------------------------- *)

fun score freqd a = 1.0 / Real.fromInt (dfind a freqd);
fun scorepa freqd (p,al) = sum_real (map (score freqd) al);

fun symdiff_ordered cmp l1 l2 = case (l1,l2) of
    ([],x) => x
  | (x,[]) => x
  | (a1 :: m1, a2 :: m2) => 
    (
    case cmp (a1,a2) of
       EQUAL => symdiff_ordered cmp m1 m2 
     | LESS => a1 :: symdiff_ordered cmp m1 l2
     | GREATER => a2 :: symdiff_ordered cmp l1 m2
    )
   
fun distance freqd ((p1,al1),(p2,al2)) = 
  sum_real (map (score freqd) (symdiff_ordered ibcmp al1 al2))
  
fun random_pair d palv = 
  let 
    val a = random_int (0,Vector.length palv - 2)
    val b = random_int (a+1,Vector.length palv - 1)
  in
    if emem (a,b) (!d) 
    then random_pair d palv 
    else (d := eadd (a,b) (!d); (a,b))
  end

fun closest_neighbor_rand freqd pal =
  let 
    val iicmp = cpl_compare Int.compare Int.compare
    val palv = Vector.fromList pal
    val d = ref (eempty iicmp)
    val l0 = mk_fast_set iicmp
      (List.tabulate (100000, fn _ => random_pair d palv))
    val l1 = map (fn (a,b) => 
      (Vector.sub (palv,a), Vector.sub (palv,b))) l0
    val l2 = map_assoc (distance freqd) l1
  in
    map fst (dict_sort compare_rmin l2)
  end;
  
  
fun filter_dupl seen ppl = case ppl of 
    [] => []
  | ((p1,_),(p2,_)) :: m =>
    if emem p1 seen orelse emem p2 seen 
    then filter_dupl seen m
    else hd ppl :: filter_dupl (eaddl [p1,p2] seen) m;
   
  
fun closest_neighbor freqd pal =
  let 
    val l0 = all_pairs pal 
    val l1 = map_assoc (distance freqd) l0
    val l2 = map fst (dict_sort compare_rmin l1)
  in
    l2
  end

fun get_pairl_simple pal =
  let
    val newpal = 
      if length pal mod 2 = 1 
      then random_elem pal :: pal 
      else pal
  in
    map pair_of_list (mk_batch_full 2 (shuffle pal)) 
  end

fun get_pairl freqd pal =
  (
  if length pal < 1000 then
    let
      val newpal = 
        if length pal mod 2 = 1 
        then random_elem pal :: pal 
        else pal
      val l1 = closest_neighbor freqd newpal
      val l2 = filter_dupl (eempty prog_compare) l1
    in
      l2
    end
  else
  let 
    val l1 = closest_neighbor_rand freqd pal
    val l2 = filter_dupl (eempty prog_compare) l1
    val l3 = first_n (length l2 div 10 + 1) l2
    val seld = enew prog_compare
      (List.concat (map (fn (a,b) => [fst a, fst b]) l3))
    val newpal = filter (fn (p,_) => not (emem p seld)) pal
  in
    l3 @ get_pairl freqd newpal
  end
  )
 
(* -------------------------------------------------------------------------
   Compete against closest neighbor
   ------------------------------------------------------------------------- *) 

fun winnerf freqd (pa1,pa2) = 
  case cpl_compare Real.compare prog_compare_size 
    ((scorepa freqd pa1, fst pa1), (scorepa freqd pa2, fst pa2)) of
    EQUAL => pa1
  | LESS => pa2
  | GREATER => pa1;  


(* -------------------------------------------------------------------------
   Parallelization of gen_progl
   ------------------------------------------------------------------------- *)

fun genprog_fun anuml pgenl = 
  let
    val (rl,pid) = gen_progl anuml pgenl
    val pl = map fst (dict_sort compare_imin (dlist pid))
  in
    (rl,pl)
  end

fun write_il file il = writel file (map its il)
fun read_il file = map string_to_int (readl file)

fun string_of_apil (a,pil) = 
  String.concatWith " " (map its (a :: pil))  

fun string_of_rlone (p,al) =
  gpt_of_prog p ^ "," ^ String.concatWith "," (map string_of_apil al)

fun write_genprogoutput file (rl, pl) = 
  (
  writel (file ^ "_rl") (map string_of_rlone rl);
  write_progl (file ^ "_pl") pl
  )
  
fun apil_of_string s = 
  let val sl = String.tokens Char.isSpace s in
    (string_to_int (hd sl), map string_to_int (tl sl))
  end
  
fun rlone_of_string s = 
  let val sl = String.tokens (fn x => x = #",") s in  
    (prog_of_gpt (hd sl), map apil_of_string (tl sl)) 
  end
  
fun read_genprogoutput file = 
  (map rlone_of_string (readl (file ^ "_rl")),
   read_progl (file ^ "_pl"))

val genprogspec : (int list, prog list, 
  (prog * (int * int list) list) list * prog list) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "search.genprogspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = genprog_fun,
  write_param = write_il,
  read_param = read_il,
  write_arg = write_progl,
  read_arg = read_progl,
  write_result = write_genprogoutput,
  read_result = read_genprogoutput
  }

fun merge_genprogrl l =
  let 
    val pid = ref (dempty prog_compare)
    fun f (rl,pl) =
      let 
        val pv = Vector.fromList pl
        fun rename iold = 
          let val p = Vector.sub (pv,iold) in
            case dfindo p (!pid) of SOME i => i | NONE =>
            let val i = dlength (!pid) in
              pid := dadd p i (!pid); i   
            end
          end
        fun g (p,aill) = 
          let fun h (a,il) = (a, map rename il) in
            (p, map h aill)
          end
      in
        map g rl
      end
    val rlmerge = List.concat (map f l)
  in
    (rlmerge, !pid)
  end     
        


fun parallel_genprog anuml pl =
  let  
    val dir = selfdir ^ "/genprog"
    val _ = clean_dir dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 10000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val pll = cut_n (4*ncore) pl
    val (l,t) = add_time 
      (smlParallel.parmap_queue_extern ncore genprogspec anuml) pll
  in
    writel (dir ^ "/log") ["time: " ^ rts t];
    merge_genprogrl l
  end

(* -------------------------------------------------------------------------
   All-in-one round
   ------------------------------------------------------------------------- *)


 
fun random_roundl n start =
  let 
    val easyl = map string_to_int (readl (selfdir ^ "/data/oeis_order"))
    val hardl = map fst oseql
    val roundl = create_round n start easyl hardl
  in
    roundl
  end

fun logt s t = print_endline (s ^ ": " ^ rts_round 4 t ^ " seconds")


fun round_one round oldwinnerl =
  let
    val winnerd = dnew prog_compare oldwinnerl
    val pid = ref (dempty prog_compare)
    val _ = print_endline ("gen_progl: " ^ its (dlength winnerd) ^ 
      " program generators")
    val ((ppl,pid),t) = 
      add_time (parallel_genprog round) (map fst oldwinnerl)
    val _ = logt "gen_progl" t
    val pl = dkeys pid
    val _ = print_endline ("eval_prog: " ^ its (dlength pid) ^ " programs")
    val (oldevall,t) = add_time (map_assoc eval_prog) pl
    val evall = map_fst (fn p => dfind p pid) oldevall
    val evald = dnew Int.compare evall
    val _ = logt "eval_prog" t
    val oldpal = map_snd (expand_ipll evald) ppl      
    fun f (p,al) = (p, mk_fast_set ibcmp (dfind p winnerd @ al))
    val pal = map f oldpal
    val freqd = count_dict (dempty ibcmp) (List.concat (map snd pal))
    val (pairl,t) = add_time get_pairl_simple pal
    val _ = logt "pairl" t
    val (solself,sol) = partition snd (dkeys freqd)
    val _ = print_endline ("solself: " ^ its (length solself))
    val _ = print_endline ("sol: " ^ its (length sol))
    val winnerl = map (winnerf freqd) pairl
  in
    winnerl
  end

fun round_loop winnerl roundl hist = case roundl of
    [] => winnerl :: hist
  | round :: newroundl => 
    let 
      val _ = print_endline ("Round " ^ its (length roundl))
      val newhist = winnerl :: hist
      val newwinnerl = round_one round winnerl
    in
      round_loop newwinnerl newroundl newhist
    end

fun competition n = 
  let 
    val winnerl = map_assoc (fn x => []) (random_pgenl (int_pow 2 n) 0.1)
    val (roundl,t) = add_time (random_roundl n) 1
    val _ = logt "random_roundl" t
    val winnerhist = round_loop winnerl roundl []
  in
    winnerhist
  end


fun stats hist =
  let 
    val histlin = List.concat hist 
    val freqd = count_dict (dempty ibcmp) (List.concat (map snd histlin))
    val (solself,sol) = partition snd (dkeys freqd)
    val _ = print_endline ("solself: " ^ its (length solself))
    val _ = print_endline ("sol: " ^ its (length sol))
  in
    ()
  end

fun competition_pl n pl =
  let 
    val winnerl = map_assoc (fn _ => []) pl
    val (roundl,t) = add_time (random_roundl n) 1
    val _ = logt "random_roundl" t
    val winnerhist = round_loop winnerl roundl []
    val _ = stats winnerhist
  in
    map fst (hd winnerhist)
  end


end (* struct *)


(* 
PolyML.print_depth 0;
load "exec_prnn"; load "search"; open kernel aiLib search bloom exec_prnn; 
PolyML.print_depth 10;

val winnerhist = competition 14;

parallelize gen_progl and eval_prog
optional: order the randomly generated programs by their values.


  
  
stats (first_n 10 winnerhist);
  
split the programs: to have the full competition because
it looks good.
execute the program inside the threads with one cache per thread.  
  
have 4096 winners  
2^12
2^24 do 12 round.  
need program compression for larger number or more memory.


select a random program and a random sequence 
(do it without parallelization first).

first time: only select programs that generate at least one new program.
compare to the set of generated programs.

this might take forever.




*)













































