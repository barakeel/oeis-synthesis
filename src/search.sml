structure search :> search =
struct

open HolKernel boolLib aiLib kernel bloom mlTreeNeuralNetwork tnn 
  exec check bloom
val ERR = mk_HOL_ERR "search"
type emb = real vector

val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)



(* todo: remove exec.exec field as it is not used anymore *)
type boarde = (kernel.prog * exec.exec * emb * emb) list
val randsearch_flag = ref false
val rand_exp = ref 1.0

(* -------------------------------------------------------------------------
   Noise (not used anymore)
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

val movel_default = List.tabulate (Vector.length operv, I)
val movel_glob = ref movel_default

fun available_move boarde move =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity boarde 
  in
    length l1 = arity 
  end
  
fun available_movel boarde = filter (available_move boarde) (!movel_glob)

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
        handle Subscript => raise ERR "operv1" 
          (its (Vector.length operv) ^ " " ^ its move)
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
    let val _ = (incr prog_counter; checkonline nnvalue (p,exec)) in
      (boarde, List.mapPartial (collect_child boarde) (!movel_glob))
    end  
  | _ => (boarde, List.mapPartial (collect_child boarde) (!movel_glob))

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
   Distributing visits in advance according to policy part of MCTS formula
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;

fun best_el dis =
  let 
    fun loop (maxel,maxsc) dis = case dis of
        [] => maxel
      | (el,(sc:real)) :: m => 
        if sc > maxsc then loop (el,sc) m else loop (maxel,maxsc) m
  in
    loop (hd dis) (tl dis)
  end;
  
fun best_n_aux acc n dis =
  if n <= 0 then acc else
  let 
    val el = best_el dis 
    val newdis = filter (fn (x,_) => x <> el) dis
  in
    best_n_aux (el :: acc) (n - 1) newdis
  end;
  
fun best_n n dis = best_n_aux [] n dis;

(* range from 1 to 1000000 *)
fun split_vis hiddenl nvis distop = 
  let
    fun h i x = if mem i hiddenl then 0 else x
    val disl = mapi h distop           
    val denom = sum_int disl
    val visl = map (fn x => (x * nvis) div denom) disl
    val visa = Array.fromList visl
    val extra = nvis - sum_int visl
    fun f i x = (i, int_div ((x * nvis) mod denom) denom)
    val fracl = mapi f disl
    val extral = best_n extra fracl
    fun g i = Array.update (visa,i, Array.sub(visa,i) + 1)
  in
    app g extral;
    visa
  end;
  (* 
   two steps, second step: forces 0 where program terminated 
   don't move them to 1 in case the distribution is all 0
  *)


val (visa,t) = add_time (split_vis [] 1000000) (List.tabulate (10,I));
val hiddenl = [0,1];

val (hiddentruel,hiddenfalsel) = 
  partition (fn x => Array.sub (visa,x) > 0) hiddenl;


val (visa2,t) = add_time (split_vis hiddenl (1000000 - (length hiddentruel))) 
  (List.tabulate (10,I));
rts t;

*)

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
  if depth >= maxproglen_treesearch then () else
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
      if !randsearch_flag orelse !notarget_flag
      then Vector.fromList [100.0] 
      else get_targete ()
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
    val targete = 
      if !randsearch_flag orelse !notarget_flag
      then Vector.fromList [100.0] 
      else get_targete ()
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
                 handle Subscript => raise ERR "operv" ""
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
  if move = maxmove then boarde else
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
      handle Subscript => raise ERR "pol2" ""
    val pol3 = normalize_distrib pol2
    val pol4 = if !game.noise_flag then add_noise pol3 else pol3
  in
    pol4
  end
  
fun beamsearch_aux targete maxwidth maxdepth depth beaml =
  if all snd beaml orelse depth >= maxdepth then () else  
  let 
    fun f ((boarde,sc),stopb) =
      if stopb then [((boarde,maxmove),sc)] else
      let 
        val ml = available_movel boarde 
        val pol = create_pol targete boarde ml
        fun g (m,msc) = ((boarde,m),sc * msc)
      in
        map g pol
      end 
    val beaml1 = dict_sort compare_rmax (List.concat (map f beaml))
    val beaml2 = first_n maxwidth beaml1
    fun h ((boarde,m),sc) = ((apply_move m boarde, sc), m=maxmove)
    val beaml3 = map h beaml2
  in
    beamsearch_aux targete maxwidth maxdepth (depth + 1) beaml3
  end

fun beamsearch () =  
  let 
    val _ = progd := eempty prog_compare
    fun f () =
      let 
        val _ = select_random_target ()
        val targete = get_targete ()
      in
        beamsearch_aux targete beam_width maxproglen 0 [(([],1.0),false)]
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
   Generation of programs
   ------------------------------------------------------------------------- *)

val mimic_time = ref 0.0
val exec_time = ref 0.0
val nullprog = [IntInf.fromInt (~1)]
val million = IntInf.fromInt 1000000

fun init_timer_wtim tim = 
  (push_counter := 0; abstimer := 0; timelimit := tim);

fun get_proba token embv = 
  let
    fun f x = IntInf.toInt (if x > million then million 
                            else if x < 1 then 1 else x)
    val v = Vector.map (f o hd) embv
    val sum = Vector.foldl (op +) 0 v
    val proba = int_div (Vector.sub (v, IntInf.toInt token)) sum
  in
    proba
  end

fun mimic_loop (exec,reset) embv (ptokl,tok,ntokl) (probaadd,probamult) =
  let 
    val _ = exec_prnn.prog_glob := (if null ptokl then nullprog else ptokl)
    val _ = exec_prnn.embv_glob := embv
    val _ = reset ()
    val _ = init_timer_wtim 100000
    fun f0 token = exec ([IntInf.fromInt token],[0]) 
    fun f1 () = SOME (Vector.tabulate (16,f0)) handle 
        Empty => NONE
      | Div => NONE
      | ProgTimeout => NONE
      | Overflow => NONE
      | Subscript => NONE
  in
    case total_time exec_time f1 () of NONE => (probaadd,0.0) | SOME newembv => 
    let 
      val proba = get_proba tok newembv
      val newprobaadd = probaadd + proba
      val newprobamult = probamult * proba  
    in
      case ntokl of 
        [] => (newprobaadd,newprobamult)
      | newtok :: newntokl =>
        mimic_loop (exec,reset) newembv (tok :: ptokl,newtok,newntokl) 
          (newprobaadd,newprobamult)
    end
  end
   
val nullemb = [IntInf.fromInt (~1)] 
val initembv = Vector.tabulate (16, fn _ => nullemb)

fun mimic execr (seq,tokl) =
  let val _ = exec_prnn.seq_glob := seq in
    mimic_loop execr initembv ([],hd tokl,tl tokl) (0.0,1.0)
  end

(* -------------------------------------------------------------------------
   Parallelization functions for generating programs
   ------------------------------------------------------------------------- *)

fun reportt s timeref =
  print_endline (s ^ ": " ^ rts_round 6 (!timeref) ^ " seconds")

fun report_all () = 
  (
  reportt "mimic" mimic_time;
  reportt "exec" exec_time
  )

fun mimic_one scref execr (anum,p) =
  let
    val seq = valOf (Array.sub (bloom.oseq,anum))
    val tokl = map IntInf.fromInt (rev (tokenl_of_prog p))
    val (sc,proba) = total_time mimic_time (mimic execr) (seq,tokl)
  in
    scref := !scref + sc 
  end 
  
fun mimic_list ex g = 
  let 
    val (exec,reset) = exec_prnn.mk_exec g
    val scref = ref 0.0
    val _ = app (mimic_one scref (exec,reset)) ex
  in
    !scref
  end  
  
fun mimic_all ex gl = 
  let
    val rl = map (mimic_list ex) gl
    val _ = report_all () 
  in
    rl
  end

(* -------------------------------------------------------------------------
   Competition problems
   ------------------------------------------------------------------------- *)

fun mk_batch_double size ex =
  let val (batch,cont) = part_n size ex in
    if null cont 
    then [batch] 
    else batch :: mk_batch_double (size * 2) cont
  end

fun merge_last_two l = case rev l of
    l1 :: l2 :: m => if length l1 < length l2 
                     then rev ((l1 @ l2) :: m)
                     else l
  | _ => raise ERR "merge_last_two" ""

fun random_batchl batchsize ex = 
  merge_last_two (mk_batch_double batchsize (shuffle ex))

(* -------------------------------------------------------------------------
   Parallelization of the competition
   ------------------------------------------------------------------------- *)

val string_to_real = valOf o Real.fromString
fun write_r file il = writel file (map rts il)
fun read_r file = map string_to_real (readl file)

fun string_of_aprog (anum,p) = 
  String.concatWith "," [its anum, gpt_of_prog p]
fun write_pex file pex = writel (file ^ "_pex") (map string_of_aprog pex)
fun aprog_of_string s =
  let val (s1,s2) = pair_of_list (String.tokens (fn x => x = #",") s) in
    (string_to_int s1, prog_of_gpt s2)
  end
fun read_pex file = map aprog_of_string (readl (file ^ "_pex"))

val mimicspec : ((int * prog) list, prog list, real list) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "search.mimicspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = mimic_all,
  write_param = write_pex,
  read_param = read_pex,
  write_arg = write_progl,
  read_arg = read_progl,
  write_result = write_r,
  read_result = read_r
  }

(* -------------------------------------------------------------------------
   All-in-one round
   ------------------------------------------------------------------------- *)

val logfile_glob = ref (selfdir ^ "/test")
fun log s = (append_endline (!logfile_glob) s; print_endline s)
fun logt s t = log (s ^ ": " ^ rts_round 4 t ^ " seconds")

fun parallel_genprog pex gl =
  let 
    val gll = cut_n (10*ncore) (shuffle gl)
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
     (string_to_int (dfind "search_memory" configd) handle NotFound => 8000) 
  in
    smlParallel.parmap_queue_extern ncore mimicspec pex gll
  end

fun update_pscl gd (p,sc) = 
  case dfindo p (!gd) of
    NONE => gd := dadd p sc (!gd)
  | SOME oldsc => gd := dadd p (sc + oldsc) (!gd)
 
fun merge_pscl pscl = 
  let
    val gd = ref (dempty prog_compare)
    val _ = app (update_pscl gd) pscl
  in
    dlist (!gd)
  end

fun round_one pex (oldwinnerl,oldgex) =
  let
    val _ = log ("gen_progl: " ^ its (length oldwinnerl) ^ " programs")
    val gl = map fst oldwinnerl
    val (rll,t) = add_time (parallel_genprog pex) gl
    val _ = logt "gen_progl" t
    val rl = List.concat rll
    val gscl1 = combine (gl,rl)
    val gscl2 = merge_pscl (oldwinnerl @ gscl1)
    val gscl3 = dict_sort compare_rmax gscl2
    val winnerl = first_n (length oldwinnerl div 2) gscl3
    val _ = log ("winners: " ^ its (length winnerl))
    val gex = if length winnerl <= int_pow 2 12 + 1 
              then map fst winnerl @ oldgex
              else oldgex
  in
    (winnerl,gex)
  end

fun round_loop winnerl batchl = case batchl of
    [] => winnerl
  | batch :: newbatchl => 
    let 
      val batchn = length batchl
      val _ = log ("Round " ^ its batchn)
      val newwinnerl = round_one batch winnerl
    in
      round_loop newwinnerl newbatchl
    end

fun stats_compete dir tottok (winnerl,gex) = 
  let 
    val _ = log ("pgen examples: " ^ its (length gex))
    val norml = map_snd (fn x => x / Real.fromInt tottok) 
      (dict_sort compare_rmax winnerl)
    val _ = log ("best score: " ^ rts (snd (hd norml)))
    val _ = log ("average score: " ^ rts (average_real (map snd norml)))
  in
    writel (dir ^ "/winner") 
      (map (fn (p,sc) => rts sc ^ ":" ^ gpt_of_prog p) norml);
    writel (dir ^ "/winner_human") 
      (map (fn (p,sc) => rts sc ^ ":" ^ human.humanf p) norml);
    write_progl (dir ^ "/gex") gex;
    writel (dir ^ "/gex_human") (map human.humanf gex)
  end
  
fun compete_pgenl (expname,ngen) pex gl =
  let
    val oldwinnerl = map (fn g => (g,0.0)) gl
    val expdir = selfdir ^ "/exp"
    val namedir = expdir ^ "/" ^ expname
    val searchdir = namedir ^ "/search"
    val dir = searchdir ^ "/" ^ its ngen
    val _ = logfile_glob := dir ^ "/log"
    val totex = length pex 
    val tottok = sum_int (map (prog_size o snd) pex)
    val _ = log ("number of examples: " ^ its totex)
    val _ = log ("number of tokens: " ^ its tottok)
    val prevdir = searchdir ^ "/" ^ its (ngen - 1)
    val _ = app mkDir_err [expdir,namedir,searchdir,dir]
    val _ = smlExecScripts.buildheap_dir := dir
    val batchl = random_batchl 64 pex
    val (winnerl,gex) = round_loop (oldwinnerl,[]) batchl
  in
    stats_compete dir tottok (winnerl,gex);
    gex
  end

(* 
1) start with 120,000 random program generators 
2) program generators: 
   - rewarded for creating both program generators and programs
   - population of best program generators evolve
     only select program generators from inference.
     Each program generator "winner" is asked 
     samples 1000 program generators.

3) how to do inference (during inference the "best" 10000 programs are
evaluated)
*)
(* -------------------------------------------------------------------------
   Inference of generators
   ------------------------------------------------------------------------- *)

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
    val gl = loop timtop
    val _ = randsearch_flag := false
    val _ = rand_exp := 1.0
  in
    gl
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
    val gl = loop timtop
  in
    gl
  end



end (* struct *)

