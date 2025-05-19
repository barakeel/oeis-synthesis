structure check :> check =
struct

open HolKernel Abbrev boolLib aiLib smlParallel 
  mcts kernel bloom human exec game poly tnn

val ERR = mk_HOL_ERR "check"
type anum = bloom.anum
type prog = kernel.prog
type ('a,'b) dict = ('a,'b) Redblackmap.dict

val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)
val mergedir = selfdir ^ "/merge"

(* -------------------------------------------------------------------------
   Ramsey check: to do move to its own file
   ramseyd: contains list of ramsey entries sorted by score
   ramseyh: contains the set of hashes from ramseyd
   ------------------------------------------------------------------------- *)

(* todo: define the score *)
fun ramsey_score_deprecated p = NONE

val compare_ramsey = cpl_compare Int.compare (inv_cmp prog_compare_size)
val ramseyd = ref (dempty compare_ramsey)
val ramseyh = ref (dempty Int.compare)

exception Catchableip of ramsey;

fun smallest_keyval d =
  (Redblackmap.app (fn x => raise Catchableip x) d; NONE)
  handle Catchableip r => SOME r

fun filter_ramsey () = 
  if dlength (!ramseyd) >= 10001 then 
    let val (k,v) = valOf (smallest_keyval (!ramseyd)) in
      ramseyd := drem k (!ramseyd);
      ramseyh := drem (#3 v) (!ramseyh)
    end
  else ()
  
fun update_ramseyd (ktop,vtop as (_,_,h,_)) = 
  case dfindo h (!ramseyh) of
    NONE =>
    (
    ramseyd := dadd ktop vtop (!ramseyd); 
    ramseyh := dadd h (ktop,vtop) (!ramseyh);
    filter_ramsey ()
    )
  | SOME (k,v) => 
    if compare_ramsey (ktop,k) <> GREATER then () else
    (
    ramseyd := drem k (!ramseyd);
    ramseyd := dadd ktop vtop (!ramseyd);
    ramseyh := dadd h (ktop,vtop) (!ramseyh)
    )

fun checkinit_ramsey () = 
  (ramseyd := dempty compare_ramsey; ramseyh := dempty Int.compare)

fun checkonline_ramsey (p,exec) = case ramsey_score_deprecated p of 
    NONE => ()
  | SOME sc => update_ramseyd ((~sc,p),(sc,sc,sc,sc))
 
fun checkfinal_ramsey () = dlist (!ramseyd)

fun merge_ramsey_file file = app update_ramseyd (read_ramseyl file)

fun merge_ramsey fileo = 
  let 
    val _ = checkinit_ramsey ()
    val filel = map (fn x => mergedir ^ "/" ^ x) (listDir mergedir)
    val _ = app merge_ramsey_file filel
    val _ = if isSome fileo then merge_ramsey_file (valOf fileo) else ()
  in
    checkfinal_ramsey ()
  end

(* -------------------------------------------------------------------------
   arcagi check
   ------------------------------------------------------------------------- *)

val arcagid = ref (dempty Int.compare)

fun compare_arcagi ((p1,b1,sc1),(p2,b2,sc2)) =
  cpl_compare (inv_cmp Int.compare) prog_compare_size ((sc1,p1),(sc2,p2))
    
fun insert_pbsc (p,b,sc) pbscl = case pbscl of
    [] => [(p,b,sc)]
  | (p',b',sc') :: m => 
    (
    case Int.compare (sc,sc') of
       GREATER => (p,b,sc) :: (p',b',sc') :: m
     | EQUAL => if prog_compare_size (p,p') = LESS 
                then (p,b,sc) :: m
                else (p',b',sc') :: m
     | LESS => (p',b',sc') :: insert_pbsc (p,b,sc) m
    )

fun update_arcagid (exi,p,b,sc) = 
  case dfindo exi (!arcagid) of
    NONE => arcagid := dadd exi [(p,b,sc)] (!arcagid) 
  | SOME pbscl => 
    let val newpbscl = first_n 10 (insert_pbsc (p,b,sc) pbscl) in
      arcagid := dadd exi newpbscl (!arcagid)
    end

fun checkonline_arcagi p =
  case arcagi.score (!arcagi.ex_glob) p of
      NONE => ()
    | SOME (b,sc) => update_arcagid (!arcagi.exi_glob,p,b,sc)
  
fun checkinit_arcagi () = arcagid := dempty Int.compare
fun checkfinal_arcagi () = 
    map (fn (a,(b,c,d)) => (a,b,c,d)) (distrib (dlist (!arcagid)))

fun merge_arcagi arcagil fileo = 
  let 
    val _ = checkinit_arcagi ()
    val arcagilold = if isSome fileo then read_arcagil (valOf fileo) else []
  in
    app update_arcagid (arcagil @ arcagilold);
    checkfinal_arcagi ()
  end   
      
(* -------------------------------------------------------------------------
   hanabi check: to do move to its own file
   hanabid: contains list of hanabi programs sorted by score
   hanabih: contains the set of hashes from hanabid
   ------------------------------------------------------------------------- *)

val compare_hanabi = cpl_compare Int.compare (inv_cmp prog_compare_size)
val hanabid = ref (dempty compare_hanabi)
val hanabih = ref (dempty IntInf.compare)

exception Catchable of hanabi;

fun smallest_keyval d =
  (Redblackmap.app (fn x => raise Catchable x) d; NONE)
  handle Catchable r => SOME r

fun filter_hanabi () = 
  if dlength (!hanabid) >= 10001 then 
    let val (k,h) = valOf (smallest_keyval (!hanabid)) in
      hanabid := drem k (!hanabid);
      hanabih := drem h (!hanabih)
    end
  else ()
  
fun update_hanabid (ktop,htop) = 
  case dfindo htop (!hanabih) of
    NONE =>
    (
    hanabid := dadd ktop htop (!hanabid); 
    hanabih := dadd htop ktop (!hanabih);
    filter_hanabi ()
    )
  | SOME k => 
    if compare_hanabi (ktop,k) <> GREATER then () else
    (
    hanabid := drem k (!hanabid);
    hanabid := dadd ktop htop (!hanabid);
    hanabih := dadd htop ktop (!hanabih)
    )

fun checkinit_hanabi () = 
  (hanabid := dempty compare_hanabi; hanabih := dempty IntInf.compare)
    
fun collect_id (Ins (id,pl)) = id :: List.concat (map collect_id pl)

fun checkonline_hanabi p = 
  if !rams_flag then 
    (case ramsey.ramsey_score p of NONE => () | SOME (sc,h) => 
     update_hanabid ((sc,p),h))
  else
  let val (sc,h) = hanabi.hanabi_score p in 
    if sc <= 0 then () else update_hanabid ((sc,p),h)
  end
 
fun checkfinal_hanabi () = dlist (!hanabid)

fun merge_hanabi_file file = app update_hanabid (read_hanabil file)

fun merge_hanabi fileo = 
  let 
    val _ = checkinit_hanabi ()
    val filel = map (fn x => mergedir ^ "/" ^ x) (listDir mergedir)
    val _ = app merge_hanabi_file filel
    val _ = if isSome fileo then merge_hanabi_file (valOf fileo) else ()
  in
    checkfinal_hanabi ()
  end

(* -------------------------------------------------------------------------
   Update set of solutions
   ------------------------------------------------------------------------- *)

fun prog_size_kid kid (Ins(id,pl)) = 
  (if id = kid then 100 else 1) + sum_int (map (prog_size_kid kid) pl)
fun prog_compare_size_kid kid (p1,p2) =
  cpl_compare Int.compare prog_compare 
   ((prog_size_kid kid p1,p1),(prog_size_kid kid p2,p2))
fun is_smaller_kid kid (t1,p1) (t2,p2) =
  prog_compare_size_kid kid (p1,p2) = LESS

fun score_optimal (t,p) = 
  Math.pow (Real.fromInt t, optimal_coeff) * Real.fromInt (prog_size p)

fun is_optimal (t1,p1) (t2,p2) = 
  cpl_compare Real.compare prog_compare_size 
    ((score_optimal (t1,p1), p1),(score_optimal (t2,p2),p2)) = LESS

fun is_faster (t1,p1) (t2,p2) =   
  cpl_compare Int.compare prog_compare_size ((t1,p1),(t2,p2)) = LESS

val abillion = 1000 * 1000 * 1000

fun is_smaller (t1,p1) (t2,p2) = 
  if !partial_flag then
    if t1 >= abillion andalso t2 >= abillion then
      is_faster (t1,p1) (t2,p2)
    else
    let val (b1,b2) = (t1 >= abillion, t2 >= abillion) in
      cpl_compare bool_compare prog_compare_size ((b1,p1),(b2,p2)) = LESS
    end
  else 
    (* prog_compare_size (p1,p2) = LESS *)
    triple_compare Int.compare Int.compare prog_compare 
      ((prog_size p1,t1,p1),(prog_size p2,t2,p2)) = LESS

fun find_min_loop cmpf a m = case m of
    [] => a
  | a' :: m' => find_min_loop cmpf (if cmpf a' a then a' else a)  m'

fun find_min cmpf l = case l of 
    [] => raise ERR "find_min" ""
  | a :: m => find_min_loop cmpf a m


fun update_solcmp lessfl d anum tpl = 
  let val newtpl = mk_fast_set (snd_compare prog_compare_size) 
    (map (fn x => find_min x tpl) lessfl)
  in
    d := dadd anum newtpl (!d)
  end

fun update_nomerge d anum tpl = d := dadd anum tpl (!d)

val update_smallest = update_solcmp [is_smaller]
val update_fastest = update_solcmp [is_faster]
val update_optimalonly = update_solcmp [is_optimal]
val update_sol2 = update_solcmp [is_smaller, is_faster]
val update_optimal = update_solcmp [is_smaller, is_optimal, is_faster]

fun get_pareto tpl =
  let
    val tpnl = map_assoc (fn (t,p) => prog_size p) tpl
    val d = dregroup Int.compare (map swap tpnl)
    val l0 = map snd (dlist d)
    fun get_best l = 
      hd (dict_sort (cpl_compare Int.compare prog_compare_size) l)
    val l1 = map get_best l0
    val r = ref []
    val mintime = ref (fst (hd l1) + 1)
    fun f (t,p) = 
      if t < (!mintime) 
      then (mintime := t; r := (t,p) :: !r)
      else ()
  in 
    app f l1; !r
  end
  
fun update_pareto d anum tpl = d := dadd anum (get_pareto tpl) (!d)

val update_solm = update_solcmp [is_smaller, is_faster, 
  is_smaller_kid 9, is_smaller_kid 12, is_smaller_kid 13]

val update_f =
  if !nomerge_flag then update_nomerge
  else if !pareto_flag then update_pareto
  else if !optimal_flag then update_optimal
  else if !optimalonly_flag then update_optimalonly
  else if !solm_flag then update_solm
  else if !sol2_flag then update_sol2
  else if !t_flag    then update_fastest
  else update_smallest
  
fun update_wind d (anum,toptpl) =
  case dfindo anum (!d) of 
    NONE => if !reprocess_select_flag 
            then update_f d anum toptpl
            else d := dadd anum toptpl (!d)
  | SOME oldtpl => update_f d anum (toptpl @ oldtpl)

fun merge_itsol itsol = 
  let val d = ref (dempty Int.compare) in
    app (update_wind d) itsol;
    dlist (!d)
  end


val compare_cov = inv_cmp Int.compare

fun update_partwind d (anum,(cov,p)) =
  case dfindo anum (!d) of 
    NONE => d := dadd anum [(cov,p)] (!d)
  | SOME oldl => 
    let
      fun test1 (oldcov,oldp) = 
        prog_compare_size (p,oldp) = LESS orelse 
        compare_cov (cov,oldcov) = LESS
      fun test2 (oldcov,oldp) =
        prog_compare_size (p,oldp) <> GREATER andalso 
        compare_cov (cov,oldcov) <> GREATER
    in
      if all test1 oldl
      then d := dadd anum ((cov,p) :: filter (not o test2) oldl) (!d) 
      else ()
    end

(* -------------------------------------------------------------------------
   Check if a program is a solution (i.e) covers an OEIS sequence
   ------------------------------------------------------------------------- *)

fun create_anumlpart (anumtl,n,anumlpart) =
  let 
    fun f (anum,_) = (anum, length (valOf (Array.sub (oseq, anum))))
    fun g anum = (anum, n)
  in
    map f anumtl @ map g anumlpart
  end
 
val wind = ref (dempty Int.compare)
val partwind = ref (dempty Int.compare)  

fun checkf nnvalue (p,exec) = 
  let
    val (anumtl,cov,anumlpart) = coverf_oeis exec
    fun f (anum,t) = 
      if !think_flag orelse !run_flag
      then update_wind wind (anum,[(Real.round (~nnvalue * 1000000000.0),p)])
      else update_wind wind (anum,[(t,p)])
    fun g (anum,n) =
      if n <= 2 then () else
      (
      if !partial_flag andalso n >= 8
      then update_wind wind (anum, [(abillion + 10000 - n, p)])
      else ()
      ;
      update_partwind partwind (anum,(n,p))
      )
  in
    app f anumtl;
    app g (create_anumlpart (anumtl,cov,anumlpart))
  end

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

fun checkf_memo nnvalue p = 
  if !nooeis_flag then 
    let 
      val ivalue = Real.round (~nnvalue * 1000000000.0)
      val cand = (ivalue,p)
      val seq' = exec_memo.penum_wtime short_timeincr p 16
      val seq = clip_seq seq'
    in
      if length seq < 16 then () else
      ( 
      case dfindo seq (!seqd) of
          NONE => seqd := dadd seq cand (!seqd)
        | SOME oldcand => 
          if cpl_compare Int.compare prog_compare_size (cand,oldcand) = LESS
          then seqd := dadd seq cand (!seqd)
          else ()
      )
    end
  else
    let
      val anumtl = exec_memo.coverp_oeis p
      fun f (anum,t) = update_wind wind (anum,[(t,p)])
    in
      app f anumtl
    end

fun checkf_ctree p = 
  let
    val exec = exec_ctree.mk_exec p 
      handle Subscript => raise ERR "checkf_ctree" "1"
    val anumtl = exec_ctree.coverf_oeis exec
      handle Subscript => raise ERR "checkf_ctree" "2"
    fun f (anum,t) = update_wind wind (anum,[(t,p)])
  in
    app f anumtl
  end  
  
fun checkf_wrat p = 
  let
    val exec = exec_wrat.mk_exec p 
      handle Subscript => raise ERR "checkf_wrat" "1"
    val anumtl = exec_wrat.coverf_oeis exec
      handle Subscript => raise ERR "checkf_wrat" "2"
    fun f (anum,t) = update_wind wind (anum,[(t,p)])
  in
    app f anumtl
  end
  
fun check_wind d (p,anumtl) =   
  let fun f (anum,t) = update_wind d (anum,[(t,p)]) in
    app f anumtl 
  end
  
fun checkf_intl (nnvalue:real) p = 
  let
    val (anumtl,cov,anumlpart) = 
      exec_intl.coverf_oeis (exec_intl.mk_exec p)
    fun f (anum,t) = 
      if !think_flag orelse !run_flag
      then update_wind wind (anum,[(Real.round (~nnvalue * 1000000000.0),p)])
      else update_wind wind (anum,[(t,p)])
    fun g (anum,n) = 
      if n <= 2 then () else
      (
      if !partial_flag andalso n >= 8
      then update_wind wind (anum, [(abillion + 10000 - n, p)])
      else ()
      ;
      update_partwind partwind (anum,(n,p))
      )
  in
    app f anumtl;
    app g (create_anumlpart (anumtl,cov,anumlpart))
  end

fun checkinit () =
  (
  wind := dempty Int.compare; 
  partwind := dempty Int.compare
  )

fun checkf_seq (p,exec) =
  let 
    val _ = (max_compr_number := 100; timeincr := 20000)
    val (b,t) = match_seq (!target_glob) exec 
  in
    if not b then () else update_wind wind (!targetn_glob,[(t,p)])          
  end
 
 
val prnnd = ref (dempty prog_compare) 
 
fun checkf_prnn nnvalue p = prnnd := dadd p nnvalue (!prnnd)

fun checkf_prnn2 p =   
  let
    val exec = fst (exec_prnn.mk_exec p)
    val anumtl = exec_prnn.coverf_oeis exec
    fun f (anum,t) = update_wind wind (anum,[(t,p)])
  in
    app f anumtl
  end  



  
val l16 = List.tabulate (16,IntInf.fromInt);

fun fingerprint f = map_total (eval_option f) l16;

val matchbackd = ref (dempty (list_compare IntInf.compare))

fun checkinit_matchback () =
  matchbackd := dempty (list_compare IntInf.compare)

fun checkonline_matchback p = 
  if depend_on_y p then () else
  let 
    val f = exec_memo.mk_exec_onev p
    val lo = fingerprint f
  in
    case lo of NONE => () | SOME l =>
    (
    case dfindo l (!matchbackd) of
      NONE => matchbackd := dadd l p (!matchbackd) 
    | SOME pold => if prog_compare_size (pold,p) = LESS then () else
                   matchbackd := dadd l p (!matchbackd)
    )
  end
  
fun checkfinal_matchback () = dlist (!matchbackd)

fun checkonline_smt p = ()

fun checkonline nnvalue (p,exec) = 
  if !smt_flag then checkonline_smt p
  else if !arcagi_flag then checkonline_arcagi p
  else if !ramsey_flag then checkonline_ramsey (p,exec)
  else if !hanabi_flag then checkonline_hanabi p
  else if !rams_flag then checkonline_hanabi p
  else if !seq_flag then checkf_seq (p,exec)
  else if !memo_flag then checkf_memo nnvalue p
  else if !ctree_flag then checkf_ctree p
  else if !wrat_flag then checkf_wrat p 
  else if !intl_flag then checkf_intl nnvalue p
  else if !prnn_flag then checkf_prnn nnvalue p
  else if !matchback_flag then checkonline_matchback p
  else checkf nnvalue (p,exec)

fun checkfinal () = dlist (!wind)
  (*
  if short_timeincr >= long_timeincr orelse 
     !seq_flag orelse !her_flag orelse !think_flag orelse !run_flag
  then  else
  let
    val _ = print_endline ("solutions: " ^ its (dlength (!wind))) 
    fun checkb p = (init_slow_test (); 
      if !intl_flag then checkf_intl 0.0 p else checkf 0.0 (p, mk_exec p))
    val bestpl0 = dlist (!partwind)
    val bestpl1 = mk_fast_set prog_compare_size 
      (map snd (List.concat (map snd bestpl0)))
    val _ = partwind := dempty Int.compare
    val _ = print_endline ("checkb: " ^ its (length bestpl1))
    val (_,t) = add_time (app checkb) bestpl1
    val _ = print_endline ("checkb time: "  ^ rts_round 2 t ^ " seconds")
    val _ = print_endline ("more solutions: " ^ its (dlength (!wind)))
  in
    dlist (!wind)
  end
  *)
  
fun collect_candidate () = 
  let 
    val pl1 = List.concat (map (map snd o snd) (dlist (!wind)))
    val pl2 = List.concat (map (map snd o snd) (dlist (!partwind)))
  in
    mk_fast_set prog_compare_size (pl1 @ pl2)
  end

fun checkf_all p =
  if !memo_flag then checkf_memo 0.0 p
  else if !ctree_flag then checkf_ctree p
  else if !intl_flag then checkf_intl 0.0 p 
  else if !wrat_flag then checkf_wrat p
  else if !prnn_flag then checkf_prnn2 p
  else checkf 0.0 (p, mk_exec p)

fun checkpl pl =
  let 
    val i = ref 0 
    fun f p = (
      init_fast_test (); incr i; 
      if !i mod 10000 = 0 then print "." else ();
      checkf_all p
      )
  in
    checkinit (); app f pl; checkfinal ()
  end

fun checkpl_target anum pl =
  let
    val rank = ref ~1
    fun update_rank i =      
      if !rank >= 0 then () else
      if dmem anum (!wind) then rank := i else ()
    fun f i p = (
      init_fast_test ();
      checkf_all p;
      update_rank i
      )
  in
    checkinit (); appi f pl; (!rank, checkfinal ())
  end  
  
  
fun next_board board move =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 <> arity 
    then NONE 
    else SOME (Ins (move, rev l1) :: l2) 
  end  
  
val movel = List.tabulate (Vector.length operv,I)  
  
fun next_boardl_aux board = 
  List.mapPartial (next_board board) movel
  
fun next_boardl boardl = List.concat (map next_boardl_aux boardl)

(* local search *)
local 
  val movelg = List.tabulate (Vector.length operv, I)
  fun available_move board move =
    let 
      val arity = arity_of_oper move
      val (l1,l2) = part_n arity board
    in
      length l1 = arity 
    end
  fun available_movel board = filter (available_move board) movelg
  fun apply_move1 move board =
    let 
      val arity = arity_of_oper move
      val (l1,l2) = part_n arity board
    in
      if length l1 <> arity 
      then raise ERR "apply_move" ""
      else (Ins (move, rev l1))
    end
in
  fun local_search d board =
    let fun f m = let val p = apply_move1 m board in d := eadd p (!d) end in
      app f (available_movel board)
    end
end
(* end local search *)

fun checkmll mll = 
  let 
    val d = ref (eempty prog_compare)
    val lr = ref []
    val error = ref 0 
    val counter = ref 0
    fun collect board movel = 
        (
        (case board of p :: m => d := eadd p (!d) | _ => ())
        ;
        (if not (!locsearch_flag) then () else local_search d board)
        ;
        case movel of [] => () | move :: m => 
          (case next_board board move of
            SOME newboard => collect newboard m 
          | NONE => incr error)    
        )
    val (_,t) = add_time (app (collect [])) mll
    val _ = print_endline ("parse errors: " ^ its (!error))
    val _ = print_endline ("parsed programs: " ^ its (elength (!d))
      ^ " in " ^ rts_round 2 t)
    fun f p =
      (incr counter; 
       if !counter mod 10000 = 0 then print "." else ();
       init_slow_test (); 
       if !memo_flag then checkf_memo 0.0 p else
       if !ctree_flag then checkf_ctree p else
       if !wrat_flag then checkf_wrat p else
       if !intl_flag then checkf_intl 0.0 p else checkf 0.0 (p, mk_exec p))
    val (_,t) = add_time (Redblackset.app f) (!d) 
  in
    print_endline ("slow check: " ^ rts_round 2 t)
  end

fun check_file file =
  let 
    val f = if !reverse_nmtoutput then rev else I
    val mll = map (f o tokenl_of_gpt) (readl file)
    val _ = print_endline (file ^ ":" ^ its (length mll))
  in
    checkmll mll; 
    let 
      val _ = print_endline ("solutions: " ^ its (dlength (!wind)))
      val r = dlist (!wind)
    in
      checkinit (); r
    end
  end

(* -------------------------------------------------------------------------
   Merging solutions from the merge directory
   ------------------------------------------------------------------------- *)

val mergen = ref 0
fun init_merge () = (mergen := 0; clean_dir mergedir) 

fun merge_itsol_file d file =
  let val itsol = read_itprogl file in
    app (update_wind d) itsol
  end
  
fun merge_itsol_default dir = 
  let 
    fun log s = (print_endline s; append_endline (dir ^ "/log") s)
    val filel = map (fn x => mergedir ^ "/" ^ x) (listDir mergedir)
    val d = ref (dempty Int.compare)
    val _ = app (merge_itsol_file d) filel
    val _ = log ("sol: " ^ its (dlength (!d)))
    val oldsolfile = dir ^ "/" ^ "solold"
    val _ = if !reprocess_flag orelse 
                not (exists_file oldsolfile) then ()
            else merge_itsol_file d oldsolfile
    fun f (anum,tpl) = 
      if length tpl <= 2 then (anum,tpl) else
      if pareto_number = 2 then (anum, [hd tpl,last tpl]) else
        let 
          val middle = butlast tpl
          val newtpl = 
            map hd (cut_n (pareto_number - 1) middle) @ [last tpl]
        in
          (anum,newtpl)
        end
  in
    if !pareto_flag andalso pareto_number >= 2 
      then map f (dlist (!d))
      else dlist (!d)
  end


(* -------------------------------------------------------------------------
   Parallel checking (two phases)
   ------------------------------------------------------------------------- *)

val checkspec : (unit, string, (anum * (int * prog) list) list) extspec =
  {
  self_dir = selfdir,
  self = "check.checkspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = let fun f () file = check_file file in f end,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = let fun f file arg = writel file [arg] in f end,
  read_arg = let fun f file = hd (readl file) in f end,
  write_result = write_itprogl,
  read_result = let fun f file = 
    (cmd_in_dir selfdir ("cp " ^ file ^ " " ^ mergedir ^ "/" ^ its (!mergen)); 
     incr mergen; 
     [])
    in f end
    }

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun stats_sol file itsol =
  let
    fun string_of_tp (t,p) =
       "size " ^ its (prog_size p) ^ ", time " ^ its t ^ ": " ^ 
       humanf p ^ "\n" ^ gpt_of_prog p
    fun string_of_itprog (i,tpl) = 
      "https://oeis.org/" ^ "A" ^ its i ^ " : " ^ 
      string_of_seq (valOf (Array.sub (oseq,i))) ^ "\n" ^ 
      String.concatWith "\n" (map string_of_tp tpl)
    val itsolsort = dict_sort 
      (snd_compare (list_compare (snd_compare prog_compare_size))) itsol
  in
    writel file (map string_of_itprog itsolsort)
  end
  
fun stats_dir dir oldsol newsol =
  let
    fun log s = (print_endline s; append_endline (dir ^ "/log") s)
    val oldset = enew Int.compare (map fst oldsol);
    val diff = filter (fn x => not (emem (fst x) oldset)) newsol;
  in
    log ("sol+oldsol: " ^ its (length newsol));
    stats_sol (dir ^ "/stats_sol") newsol;
    log ("diff: " ^ its (length diff));
    stats_sol (dir ^ "/stats_diff") diff
  end

fun write_gptsol file sol =
  let
    fun f (i,tpl) =
      let 
        val seqs = gpt_of_seq (rev (first_n 16 (valOf (Array.sub (oseq,i))))) 
        fun g (t,p) = seqs ^ ">" ^ gpt_of_prog p
      in
        map g tpl
      end
  in
    writel file (shuffle (List.concat (map f sol)))
  end

fun parallel_check expname = 
  let 
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = mkDir_err dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val splitdir = dir ^ "/split"
    val oldsol = read_itprogl (dir ^ "/" ^ "solold")
    val _ = if not (!reprocess_flag) then () else
      let
        val oldprogl = mk_fast_set prog_compare 
          (map snd (List.concat (map snd oldsol)))
        val oldprogl_file = dir ^ "/" ^ "solold_reprocess"
      in
        writel oldprogl_file
        (map (implode o rev o explode o gpt_of_prog) oldprogl)
      end
    val _ = mkDir_err splitdir
    val _ = 
      if !reprocess_flag 
      then (
           cmd_in_dir dir "cat cand solold_reprocess > candx1";
           cmd_in_dir dir "split -l 10000 candx1 split/cand";
           cmd_in_dir dir "rm candx1"
           )
      else cmd_in_dir dir "split -l 10000 cand split/cand"
    val filel = map (fn x => splitdir ^ "/" ^ x) (listDir splitdir) 
    fun log s = (print_endline s; append_endline (dir ^ "/log") s)
    val _ = init_merge ()
    val (_,t) = add_time (parmap_queue_extern ncore checkspec ()) 
      (rev filel)
    val _ = log ("checking time: " ^ rts_round 6 t)
    val (newsol,t) = add_time merge_itsol_default dir
    val _ = log ("merging time: " ^ rts_round 6 t)
    val _ = init_merge ()
    val gptfile = dir ^ "/" ^ "solnewgpt" 
    val newsolfile = dir ^ "/" ^ "solnew"
    
  in
    stats_dir dir oldsol newsol;
    write_itprogl (newsolfile ^ "_temp") newsol;
    write_gptsol (gptfile ^ "_temp") newsol;
    OS.FileSys.rename {old = newsolfile ^ "_temp", new = newsolfile};
    OS.FileSys.rename {old = gptfile ^ "_temp", new = gptfile}
  end
  
(* -------------------------------------------------------------------------
   Check if a program generate OEIS programs
   ------------------------------------------------------------------------- *)

(* data structures 
pgenS: contains list of pgen entries keyed by score (and program size)
pgenA: contains list of pgen entries with keys being a list of A numbers
checks if a new entry is strictly subsumed by existing entries 
*)

val compare_scp = cpl_compare Int.compare (inv_cmp prog_compare_size)
val pgenS = ref (dempty compare_scp)
val pgenA = ref (dempty (list_compare Int.compare))

(* assumes increasing list *)
fun included_in l1 l2 = case (l1,l2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => 
    if a2 < a1 then included_in l1 m2 else
    if a2 = a1 then included_in m1 m2
    else false
    
exception Catchableip of ((int * kernel.prog) * pgen);
fun smallest_keyval d =
  (Redblackmap.app (fn x => raise Catchableip x) d; NONE)
  handle Catchableip r => SOME r

(* determining if a new candidate is worth inserting *)
fun test_pgen (p,ipl) =
  if null ipl then false else
  if dlength (!pgenS) <= 0 then true else 
  let 
    val newkS = (length ipl, p)
    val newkA = map fst ipl
    val (smallkS,_) = valOf (smallest_keyval (!pgenS)) 
  in
    if compare_scp (smallkS,newkS) = LESS then  
      (
      case dfindo newkA (!pgenA) of
          NONE => all (not o (included_in newkA)) (dkeys (!pgenA))
        | SOME vA => prog_compare_size (p, fst vA) = LESS
      )
    else false
  end
  
fun filter_pgen () = 
  if dlength (!pgenS) <= 10000 then () else 
  let 
    val (kS,vS) = valOf (smallest_keyval (!pgenS)) 
    val kA = map fst (snd vS)
  in
    pgenS := drem kS (!pgenS);
    pgenA := drem kA (!pgenA)
  end 

fun insert_pgen pgen =
  if not (test_pgen pgen) then () else
  let
    val newkA = map fst (snd pgen)
    val newkS = (length (snd pgen), fst pgen)
    val coveredl = filter (fn (kA,_) => included_in kA newkA) (dlist (!pgenA))
    val kAl = map fst coveredl
    val kSl = map (fn (_,(p,ipl)) => (length ipl, p)) coveredl
  in
    (* removing *)
    app (fn x => pgenA := drem x (!pgenA)) kAl;
    app (fn x => pgenS := drem x (!pgenS)) kSl;
    (* adding *)
    pgenA := dadd newkA pgen (!pgenA);
    pgenS := dadd newkS pgen (!pgenS);
    (* removing *)
    filter_pgen ();
    if dlength (!pgenA) <> dlength (!pgenS) 
      then raise ERR "insert_pgen" "assumption"
      else ()
  end

fun checkinit_pgen () = 
  (pgenS := dempty compare_scp; pgenA := dempty (list_compare Int.compare))
  
fun checkonline_pgen (p,exec) =
  let val ipl = penum_pgen exec in
    insert_pgen (p,ipl)
  end
 
fun checkfinal_pgen () = map snd (dlist (!pgenS))

fun merge_pgen_file file = app insert_pgen (read_pgen file)

fun merge_pgen fileo = 
  let 
    val _ = checkinit_pgen ()
    val filel = map (fn x => mergedir ^ "/" ^ x) (listDir mergedir)
    val _ = app merge_pgen_file filel
    val _ = if isSome fileo then merge_pgen_file (valOf fileo) else ()
  in
    checkfinal_pgen ()
  end  


end (* struct *)
