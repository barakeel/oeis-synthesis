structure check :> check =
struct

open HolKernel Abbrev boolLib aiLib smlParallel 
  mcts kernel bloom human exec game poly tnn

val ERR = mk_HOL_ERR "check"
type anum = bloom.anum
type prog = kernel.prog
type ('a,'b) dict = ('a,'b) Redblackmap.dict

(* -------------------------------------------------------------------------
   Update set of solutions
   ------------------------------------------------------------------------- *)

val partial_flag = bflag "partial_flag"
val abillion = 1000000000

fun is_faster (t1,p1) (t2,p2) =   
  cpl_compare Int.compare prog_compare_size ((t1,p1),(t2,p2)) = LESS

fun is_smaller (t1,p1) (t2,p2) = 
  if !partial_flag then
    if t1 >= abillion andalso t2 >= abillion then
      is_faster (t1,p1) (t2,p2)
    else
    let val (b1,b2) = (t1 >= abillion, t2 >= abillion) in
      cpl_compare bool_compare prog_compare_size ((b1,p1),(b2,p2)) = LESS
    end
  else prog_compare_size (p1,p2) = LESS

fun find_min_loop cmpf a m = case m of
    [] => a
  | a' :: m' => find_min_loop cmpf (if cmpf a' a then a' else a)  m'

fun find_min cmpf l = case l of 
    [] => raise ERR "find_min" ""
  | a :: m => find_min_loop cmpf a m


fun update_ifnew d anum (tpl,newtpl) = 
  if list_compare (snd_compare prog_compare) (tpl,newtpl) = EQUAL 
  then () 
  else d := dadd anum newtpl (!d)

fun update_smallest d anum tpl =
  let val newtpl = [find_min is_smaller tpl] in
    update_ifnew d anum (tpl,newtpl)
  end
  
fun update_fastest d anum tpl =
  let val newtpl = [find_min is_faster tpl] in
    update_ifnew d anum (tpl,newtpl)
  end  
   
fun update_sol2 d anum tpl =
  let val newtpl = mk_fast_set (snd_compare prog_compare) 
    [find_min is_smaller tpl, find_min is_faster tpl]
  in
    update_ifnew d anum (tpl,newtpl)
  end

fun update_wind d (anum,toptpl) =
  case dfindo anum (!d) of 
    NONE => d := dadd anum toptpl (!d)
  | SOME oldtpl =>
    let val tpl = toptpl @ oldtpl in
      if !sol2_flag then update_sol2 d anum tpl
      else if !t_flag then update_fastest d anum tpl
      else update_smallest d anum tpl
    end

fun merge_itsol itsol = 
  let val d = ref (dempty Int.compare) in
    app (update_wind d) itsol;
    dlist (!d)
  end

fun compare_to (t1,t2) = case (t1,t2) of
    (NONE,NONE) => EQUAL
  | (SOME _, NONE) => LESS
  | (NONE, SOME _) => GREATER
  | (SOME x1, SOME x2) => Int.compare (x1,x2)

fun inv_cmp cmp (a,b) = cmp (b,a)
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


fun checkf (p,exec) = 
  let
    val (anumtl,cov,anumlpart) = coverf_oeis exec
    fun f (anum,t) = update_wind wind (anum,[(t,p)])
    fun g (anum,n) = 
      if n <= 2 then () else
      (
      if !partial_flag 
      then update_wind wind (anum, [(abillion + 10000 - n, p)])
      else ()
      ;
      update_partwind partwind (anum,(n,p))
      )
  in
    app f anumtl;
    app g (create_anumlpart (anumtl,cov,anumlpart))
  end

fun checkonline (p,exec) = (init_fast_test (); checkf (p,exec))
fun checkinit () = (wind := dempty Int.compare; partwind := dempty Int.compare)

fun checkfinal () =
  let
    val _ = print_endline ("solutions: " ^ its (dlength (!wind))) 
    fun checkb p = (init_slow_test (); checkf (p, mk_exec p))
    val bestpl0 = dlist (!partwind)
    val bestpl1 = mk_fast_set prog_compare_size 
      (map snd (List.concat (map snd bestpl0)))
    val _ = partwind := dempty Int.compare
    val _ = print_endline ("checkb: " ^ its (length bestpl1))
    val (_,t) = add_time (app checkb) bestpl1
    val _ = print_endline ("checkb time: "  ^ rts_round 2 t ^ " seconds")
    val _ = print_endline ("more solutions: " ^ its (dlength (!wind)))  
    val r = dlist (!wind)
  in
    checkinit (); r
  end
  
fun collect_candidate () = 
  let 
    val pl1 = List.concat (map (map snd o snd) (dlist (!wind)))
    val pl2 = List.concat (map (map snd o snd) (dlist (!partwind)))
  in
    mk_fast_set prog_compare_size (pl1 @ pl2)
  end
  
fun checkpl pl =
  let 
    val i = ref 0 
    fun f p = (
      init_fast_test (); 
      incr i; 
      if !i mod 10000 = 0 then print "."  else ();
      checkf (p, mk_exec p)
      )
  in
    checkinit (); app f pl; checkfinal ()
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
  
val error = ref 0  

val localsearch_flag = ref false

fun checkml d board movel =
  (
  if !localsearch_flag then
    let
      val boardl = next_boardl [board]    
      fun f board = case board of p :: m => d := eadd p (!d) | _ => ()
    in
      app f boardl
    end
  else (case board of p :: m => d := eadd p (!d) | _ => ())
  ;
    case movel of [] => () | move :: m => 
      (case next_board board move of
        SOME newboard => checkml d newboard m 
      | NONE => incr error)    
  )  

fun checkmll mll = 
  let 
    val d = ref (eempty prog_compare)
    val counter = ref 0
    val (_,t) = add_time (app (checkml d [])) mll
    val _ = print_endline ("parse errors: " ^ its (!error))
    val _ = print_endline ("parsed programs: " ^ its (elength (!d))
      ^ " in " ^ rts_round 2 t)
    fun f p =
      (incr counter; 
       if !counter mod 10000 = 0 then print "." else ();
       init_fast_test (); checkf (p, mk_exec p))
    val (_,t) = add_time (Redblackset.app f) (!d)
  in
    print_endline ("fast check: " ^ rts_round 2 t)
  end

fun check_file file =
  let 
    val mll = map (rev o movel_of_gpt) (readl file)
    val _ = print_endline (file ^ ":" ^ its (length mll))
    val _ = error := 0
  in
    checkinit (); checkmll mll; checkfinal ()
  end


(* -------------------------------------------------------------------------
   Merging solutions from the merge directory
   ------------------------------------------------------------------------- *)

val mergen = ref 0
val mergedir = selfdir ^ "/merge"
fun init_merge () = (mergen := 0; clean_dir mergedir) 

fun merge_itsol_file d file =
  let val itsol = read_itprogl file in
    app (update_wind d) itsol
  end
  
fun merge_itsol_default dir = 
  let 
    fun log s = (print_endline s; append_endline (dir ^ "/log") s)
    val filel = map (fn x => selfdir ^ "/merge/" ^ x) (listDir mergedir)
    val d = ref (dempty Int.compare)
    val _ = app (merge_itsol_file d) filel
    val _ = log ("sol: " ^ its (dlength (!d)))
    val oldsolfile = dir ^ "/" ^ "solold"
    val _ = merge_itsol_file d oldsolfile
  in
    dlist (!d)
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

val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)

fun write_gsol file sol =
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
    val _ = mkDir_err splitdir
    val _ = cmd_in_dir dir "split -l 100000 cand split/cand"
    val filel = map (fn x => splitdir ^ "/" ^ x) (listDir splitdir) 
    fun log s = (print_endline s; append_endline (dir ^ "/log") s)
    val _ = init_merge ()
    val (_,t) = add_time (parmap_queue_extern ncore checkspec ()) filel
    val _ = log ("checking time: " ^ rts_round 6 t)
    val (newsol,t) = add_time merge_itsol_default dir
    val _ = log ("merging time: " ^ rts_round 6 t)
    val _ = init_merge ()
    val gptfile = dir ^ "/" ^ "solnewgpt" 
    val newsolfile = dir ^ "/" ^ "solnew"
    val oldsol = read_itprogl (dir ^ "/" ^ "solold")
  in
    stats_dir dir oldsol newsol;
    write_itprogl (newsolfile ^ "_temp") newsol;
    write_gsol (gptfile ^ "_temp") newsol;
    OS.FileSys.rename {old = newsolfile ^ "_temp", new = newsolfile};
    OS.FileSys.rename {old = gptfile ^ "_temp", new = gptfile}
  end

(* -------------------------------------------------------------------------
   Levenstein
   ------------------------------------------------------------------------- *) 
  
fun min3 (a,b,c) = Int.min (Int.min (a,b),c) 

fun lev cache (al,an) (bl,bn) = 
  let val v = Array2.sub (cache,an,bn) in 
    if v >= 0 then v else
    (
    case (al,bl) of
      ([],_) => bn
    | (_,[]) => an
    | (a :: am, b :: bm) => 
      let val r =
        if a = b then lev cache (am,an-1) (bm,bn-1) else 
        1 + min3 (lev cache (al,an) (bm,bn-1), lev cache (am,an-1) (bl,bn), 
                  lev cache (am,an-1) (bm,bn-1))
      in
        Array2.update (cache,an,bn,r); r
      end
    )
  end;

fun levenstein al bl =
  let 
    val (an,bn) = (length al, length bl)
    val cache = Array2.array (an+1,bn+1,~1) 
  in
    lev cache (al,length al) (bl,length bl)
  end;
  
fun is_similar p1 p2 =
  let 
    val (l1,l2) = (map snd (linearize p1), map snd (linearize p2)) 
    val levn = levenstein l1 l2
    val (n1,n2) = (length l1, length l2)
    val diffn = Int.abs (n1 - n2)
    val minn = Int.min (n1,n2)
  in
    int_div (levn - diffn) (minn) <= 0.2
  end

(* -------------------------------------------------------------------------
   Check if a program generates an approximation of the primes
   ------------------------------------------------------------------------- *)

val primed = ref (dempty seq_compare)

fun better_small (r1,p1) (r2,p2) = prog_compare_size (p1,p2) = LESS
val better_small_cmp = snd_compare prog_compare_size

fun better_fast (r1,p1) (r2,p2) = Int.compare (r1,r2) = LESS
val better_fast_cmp = fst_compare Int.compare

fun filter_primed () =
  let val newl = first_n 100000
    (dict_sort (snd_compare better_fast_cmp) (dlist (!primed)))
  in
    primed := dnew seq_compare newl
  end

fun update_primed (il,(r,p)) =
  (
  if dlength (!primed) > 110000 then filter_primed () else ();
  case dfindo il (!primed) of 
    NONE => primed := dadd il (r,p) (!primed) 
  | SOME (rold,pold) => 
    if better_fast (r,p) (rold,pold)
    then primed := dadd il (r,p) (!primed)
    else ()
  )

fun checkinit_prime () = primed := dempty seq_compare
  
fun checkonline_prime (p,exec) =
  let val (il,newexec) = penum_prime_exec exec in 
    (if null il then () else update_primed (il,(!abstimer,p)); newexec)
  end

fun checkfinal_prime () = (filter_primed (); dlist (!primed))

fun merge_primesol primesol = 
  let val _ = checkinit_prime () in
    app update_primed primesol;
    checkfinal_prime ()
  end 
  
(* -------------------------------------------------------------------------
   Check if a program generates hadamard matrices
   ------------------------------------------------------------------------- *)

val hdmd = ref (dempty seq_compare)

fun inv_cmp cmp (a,b) = cmp (b,a)
fun thirdel l = List.nth (l,2)
fun secondel l = List.nth (l,1)

fun hdm_compare_length ((l1,(_,p1)),(l2,(_,p2))) = 
  cpl_compare (inv_cmp IntInf.compare) prog_compare_size 
    ((thirdel l1,p1),(thirdel l2,p2))

fun filter_hdmd () =
  if dlength (!hdmd) < 21000 then () else
  let 
    val l1 = dlist (!hdmd)
    val l2 = map (fn x => (secondel (fst x),x)) l1
    val d = dregroup IntInf.compare l2
    val l3 = dlist d
    val l4 = map (first_n 1000 o dict_sort hdm_compare_length o snd) l3
  in
    hdmd := dnew seq_compare (List.concat l4)
  end

fun update_hdmd (il,(r,p)) =
  (
  filter_hdmd ();
  case dfindo il (!hdmd) of 
    NONE => hdmd := dadd il (r,p) (!hdmd) 
  | SOME (rold,pold) => 
    if better_small (r,p) (rold,pold)
    then hdmd := dadd il (r,p) (!hdmd)
    else ()
  )

fun checkinit_hdm () = hdmd := dempty seq_compare
  
fun checkonline_hdm_z (p,exec) z =
  let val il = penum_hadamard_fast exec z in
    if null il then () else update_hdmd (il,(!abstimer,p))
  end
  
fun checkonline_hdm (p,exec) =
  app (checkonline_hdm_z (p,exec)) (List.tabulate (20, fn x => 2*x + 9)) 

fun checkfinal_hdm () = (filter_hdmd (); dlist (!hdmd))

fun merge_hdmsol hdmsol = 
  let val _ = checkinit_hdm () in
    app update_hdmd hdmsol;
    checkfinal_hdm ()
  end
  
  
end (* struct *)
