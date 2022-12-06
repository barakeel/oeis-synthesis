structure def :> def =
struct

open HolKernel Abbrev boolLib aiLib kernel exec bloom smlParallel

val ERR = mk_HOL_ERR "def"
type macro = int list
type cand = prog * (int * macro)
val reverse_flag = ref true

(* -------------------------------------------------------------------------
   Macros
   ------------------------------------------------------------------------- *) 

val minop = Vector.length operv
val maxop = minop + 9
val sepop = maxop + 1
fun is_id x = x >= minop
fun contain_id m = exists (fn x => x >= minop) m
fun macro_of_string s = map id_of_gpt (String.tokens Char.isSpace s)
fun string_of_macro il = String.concatWith " " (map gpt_of_id il)

(* -------------------------------------------------------------------------
   Generate random candidates and random definitions for testing
   ------------------------------------------------------------------------- *) 

fun random_cand () =
  (List.tabulate (random_int (10,50), fn _ => random_int (0,maxop)))
fun gen_cand file n =
  let val l = List.tabulate (n, fn _ => string_of_macro (random_cand ())) in
    writel file l
  end
  
fun random_def () =
  List.tabulate (random_int (5,10), fn _ => random_int (0,minop-1))
fun gen_def n =
  let val l = List.tabulate (n, fn _ => string_of_macro (random_def ())) in
    writel (selfdir ^ "/def") l
  end  

(* -------------------------------------------------------------------------
   Converting list of indices to single index and back
   ------------------------------------------------------------------------- *)

local 
  fun lfields_aux buf acc sep l = case l of
    [] => rev (rev buf :: acc)
  | a :: m => 
    if a = sep then lfields_aux [] (rev buf :: acc) sep m
    else lfields_aux (a :: buf) acc sep m
  fun lfields sep l = lfields_aux [] [] sep l    
in 
  fun ltokens sep l = filter (fn x => not (null x)) (lfields sep l)
end

fun compress_idl idl =
  let fun loop acc lcur = 
    case lcur of [] => acc | a :: m => loop (10 * acc + a) m
  in
    minop + loop 0 (rev (map (fn y => y - minop) idl))
  end

fun lfields_aux buf acc l = case l of
    [] => rev (rev buf :: acc)
  | a :: m => 
    if null buf orelse is_id (hd buf) = is_id a 
    then lfields_aux (a :: buf) acc m
    else lfields_aux [a] (rev buf :: acc) m

fun lfields l = lfields_aux [] [] l;

fun compress_idl_safe idl =
  if null idl then [] else
  (let val i = compress_idl idl in [i] end handle Overflow => [])

fun compress_all_idl macro =
  let 
    fun f idl = 
      if not (is_id (hd idl)) then idl else
      List.concat (map compress_idl_safe (ltokens sepop idl))
  in
    List.concat (map f (lfields macro))
  end

fun expand_id_aux x =
  if x < 10 then [x] else (x mod 10) :: expand_id_aux (x div 10)

fun expand_id x = 
  map (fn y => y + minop) (expand_id_aux (x - minop)) 

fun lconcatw_aux ll = case ll of
    [] => []
  | [a] => [a]
  | a :: b :: m =>
    let val sepo = 
      if is_id (hd a) andalso is_id (hd b) then [sepop] else []
    in     
      a :: sepo :: lconcatw_aux (b :: m)
    end
 
fun lconcatw ll = List.concat (lconcatw_aux ll);
  
fun expand_all_id macro = 
  let fun f i = if is_id i then expand_id i else [i] in
    lconcatw (map f macro)
  end

(* -------------------------------------------------------------------------
   Read definitions and candidates
   ------------------------------------------------------------------------- *)

val defv = ref (Vector.fromList [])
fun read_def file = defv := 
  Vector.fromList (map (compress_all_idl o macro_of_string) (readl file))
fun write_def file = writel file
  (map (string_of_macro o expand_all_id) (vector_to_list (!defv)));  
 
fun read_cand file =
  let val macrol = map macro_of_string (readl file) in
    if !reverse_flag then map rev macrol else macrol  
  end


(* -------------------------------------------------------------------------
   Unfold and fold definitions
   ------------------------------------------------------------------------- *)

fun unfold_def_one v macro = case macro of
    [] => []
  | a :: m => 
    if is_id a 
    then Vector.sub (v, a - minop) @ unfold_def_one v m
    else a :: unfold_def_one v m

fun unfold_def v macro = 
  let val newmacro = unfold_def_one v macro in
    if newmacro = macro then macro else unfold_def v newmacro
  end

fun is_prefix_cont def macro = case (def,macro) of 
      ([],_) => SOME macro 
    | (_,[]) => NONE 
    | (a1 :: m1, a2 :: m2) => if a1 <> a2 then NONE else is_prefix_cont m1 m2

fun fold_def_one (def,defn) macro = case macro of 
    [] => []
  | a :: m =>
    (
    case is_prefix_cont def macro of
       NONE => a :: fold_def_one (def,defn) m
     | SOME cont => defn :: fold_def_one (def,defn) cont
    )

fun fold_def defidl macro = foldl (uncurry fold_def_one) macro defidl 

fun defidl_of_defv v = number_snd minop (vector_to_list v)

(* -------------------------------------------------------------------------
   Converting macro to program and vice versa
   ------------------------------------------------------------------------- *)

fun apply_move move board =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 < arity 
    then raise ERR "prog_of_macro" "arity"
    else Ins (move, rev l1) :: l2
  end

fun prog_of_macro macro = 
  let val progl = foldl (uncurry apply_move) [] macro in
    case progl of [p] => p | _ => raise ERR "prog_of_macro" "not a singleton"
  end

fun macro_of_prog_aux (Ins (id,pl)) = 
  id :: List.concat (map macro_of_prog_aux (rev pl));
fun macro_of_prog p = rev (macro_of_prog_aux p);

(* -------------------------------------------------------------------------
   Collect programs from subsequences in an unfolded macro
   ------------------------------------------------------------------------- *)

fun next_board board move =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 < arity
    then []   
    else Ins (move, rev l1) :: l2
  end
  
fun collect_aux moveltop = 
  let 
    val progl = ref []
    fun loop board movel = case movel of [] => () | move :: m => 
      let 
        val newboard = next_board board move
        val _ = if null newboard then () 
                else progl := hd newboard :: !progl
      in
        loop newboard m
      end
   in
     loop [] moveltop; !progl
   end

fun update_progd progd candl =
  let
    val cmp = cpl_compare Int.compare (list_compare Int.compare); 
    fun f (a,b) = 
      case dfindo a (!progd) of
        NONE => progd := dadd a b (!progd)
      | SOME b' => if cmp (b,b') = LESS then progd := dadd a b (!progd) else ()
  in
    app f candl
  end

fun collect progd defidl macro =
  let   
    val progl = collect_aux macro
    fun f p = 
      let val newm = expand_all_id (fold_def defidl (macro_of_prog p)) in
        (p, (length newm, newm))
      end
    val candl = map f progl
  in
    update_progd progd candl 
  end

fun extract_candl candle = 
  let
    val defidl = defidl_of_defv (!defv)
    val progd = ref (dempty prog_compare)
    val (_,t) = add_time (app (collect progd defidl)) candle
    val _ = print_endline ("extract_candl: " ^ rts_round 2 t)
  in
    dlist (!progd)
  end
 
(* -------------------------------------------------------------------------
   Test candidates (copied from macro.sml)
   ------------------------------------------------------------------------- *)

val wind = ref (dempty Int.compare)
val partwind = ref (dempty Int.compare)  
fun checkinit () = (wind := dempty Int.compare; 
                    partwind := dempty Int.compare);

fun cand_compare_size ( (p,(n,m)) : cand, (p',(n',m')) : cand) =
  cpl_compare Int.compare (list_compare Int.compare) ((n,m),(n',m'));

fun is_faster (t1,p1) (t2,p2) =   
  cpl_compare Int.compare cand_compare_size ((t1,p1),(t2,p2)) = LESS

fun is_smaller (t1,p1) (t2,p2) = 
  cand_compare_size (p1,p2) = LESS

fun find_min_loop cmpf a m = case m of
    [] => a
  | a' :: m' => find_min_loop cmpf (if cmpf a' a then a' else a)  m'

fun find_min cmpf l = case l of 
    [] => raise ERR "find_min" ""
  | a :: m => find_min_loop cmpf a m

fun update_smallest d anum tpl =
  let val newtpl = [find_min is_smaller tpl] in
    d := dadd anum newtpl (!d)
  end 
fun update_fastest d anum tpl =
  let val newtpl = [find_min is_faster tpl] in
    d := dadd anum newtpl (!d)
  end  
fun update_sol2 d anum tpl =
  let val newtpl = mk_fast_set (snd_compare cand_compare_size) 
    [find_min is_smaller tpl, find_min is_faster tpl]
  in
    d := dadd anum newtpl (!d)
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

fun inv_cmp cmp (a,b) = cmp (b,a)
val compare_cov = inv_cmp Int.compare

fun update_partwind d (anum,(cov,p)) =
  case dfindo anum (!d) of 
    NONE => d := dadd anum [(cov,p)] (!d)
  | SOME oldl => 
    let
      fun test1 (oldcov,oldp) = 
        cand_compare_size (p,oldp) = LESS orelse 
        compare_cov (cov,oldcov) = LESS
      fun test2 (oldcov,oldp) =
        cand_compare_size (p,oldp) <> GREATER andalso 
        compare_cov (cov,oldcov) <> GREATER
    in
      if all test1 oldl
      then d := dadd anum ((cov,p) :: filter (not o test2) oldl) (!d) 
      else ()
    end

fun create_anumlpart (anumtl,n,anumlpart) =
  let 
    fun f (anum,_) = (anum, length (valOf (Array.sub (oseq, anum))))
    fun g anum = (anum, n)
  in
    map f anumtl @ map g anumlpart
  end

fun checkf (p,exec) = 
  let
    val (anumtl,cov,anumlpart) = coverf_oeis exec
    fun f (anum,t) = update_wind wind (anum,[(t,p : cand)])
    fun g (anum,n) = 
      if n <= 2 then () else update_partwind partwind (anum,(n,p : cand))
  in
    app f anumtl;
    app g (create_anumlpart (anumtl,cov,anumlpart))
  end;

fun checkonline (p,exec) = (init_fast_test (); checkf (p,exec));

fun checkfinal () =
  let
    fun checkb p = (init_slow_test (); checkf (p, mk_exec (fst p)))
    val bestpl0 = dlist (!partwind)
    val bestpl1 = mk_fast_set cand_compare_size 
      (map snd (List.concat (map snd bestpl0)))
    val _ = partwind := dempty Int.compare
    val _ = print_endline ("check slow: " ^ its (length bestpl1))
    val (_,t) = add_time (app checkb) bestpl1
    val _ = print_endline ("check slow time: "  ^ rts_round 2 t ^ " seconds")
    val _ = print_endline ("check slow solutions: " ^ its (dlength (!wind)))  
    val r = dlist (!wind)
  in
    checkinit (); r
  end;

fun check_candl candl =
  let 
    val i = ref 0 
    fun f p = (
      init_fast_test (); incr i; 
      if !i mod 10000 = 0 then print "." else ();
      checkf (p, mk_exec (fst p))
      )
    val _ = checkinit () 
    val (_,t) = add_time (app f) candl
    val _ = print_endline ""
    val _ = print_endline ("check fast solutions: " ^ its (dlength (!wind))) 
  in
    print_endline ("check fast time: " ^ rts_round 2 t ^ " seconds");
    checkfinal ()
  end;


(* -------------------------------------------------------------------------
   Turn frequent submacro into definitions
   ------------------------------------------------------------------------- *)

fun all_suffix l = case l of [] => [] | a :: m => l :: all_suffix m;
fun all_revprefix l = all_suffix (rev l);

fun count_subseq macrol =
  let
    val subd = ref (dempty (list_compare Int.compare))
    fun f_one macro =
      let val l = all_revprefix (first_n 240 macro) in
        subd := count_dict (!subd) l
      end
    fun f macro = case macro of [] => () | a :: m => (f_one macro; f m)
    val _ = app f macrol
  in
    map_fst rev (dlist (!subd))
  end

(* updates defv *)
fun mk_def n progl =
  if n <= 0 then () else
  let
    val v = !defv
    val defidl = defidl_of_defv v
    val defsize = length (expand_id (Vector.length v + minop))
    val prevd = enew (list_compare Int.compare) (vector_to_list v)
    val macrol = map (fold_def defidl o macro_of_prog) progl
    val l1 = count_subseq macrol
    fun score (macro,freq) = 
      if freq < 20 orelse length macro <= defsize orelse 
         length (unfold_def v macro) >= 240 orelse emem macro prevd 
      then NONE 
      else SOME (macro, (length (expand_all_id macro) - defsize) * freq)
    val l2 = List.mapPartial score l1
    val l3 = first_n 1 (map fst (dict_sort compare_imax l2))
  in
    if null l3 then () else 
    (
    print_endline (string_of_macro (expand_all_id (hd l3)));
    defv := Vector.concat [!defv, Vector.fromList l3];
    mk_def (n-1) progl
    )
  end;

(* -------------------------------------------------------------------------
   Recompute macro the set of solutions
   ------------------------------------------------------------------------- *)

fun recompute_macro sol = 
  let 
    val defidl = defidl_of_defv (!defv)
    fun g (t,(p,(n,m))) = 
      let val newm = expand_all_id (fold_def defidl (macro_of_prog p)) in
        (t,(p,(length newm,newm)))
      end
    fun f (anum,tpl) = (anum, map g tpl)
  in
    map f sol
  end
  
(* -------------------------------------------------------------------------
   Candidates I/O
   ------------------------------------------------------------------------- *)

fun string_of_tcand (t,(p,(macron,macro))) = String.concatWith "," 
   [its macron, its t, gpt_of_prog p, string_of_macro macro] 
fun string_of_itcandl (i,tcandl) =
  its i ^ "|" ^ String.concatWith "|" (map string_of_tcand tcandl)
fun write_itcandl file itcandl =
  writel file (map string_of_itcandl itcandl)
  
fun tcand_of_string s =
  let 
    val (s1,s2,s3,s4) = quadruple_of_list (String.tokens (fn c => c = #",") s) 
    val size = string_to_int s1
    val speed = string_to_int s2
    val p = prog_of_gpt s3
    val macro = macro_of_string s4
  in
    (speed,(p,(size,macro)))
  end
  
fun itcandl_of_string s =
  let val sl = String.tokens (fn c => c = #"|") s in 
    (string_to_int (hd sl), map tcand_of_string (tl sl))
  end
fun read_itcandl file = map itcandl_of_string (readl file)

(* -------------------------------------------------------------------------
   Parallel check: checking candidates
   ------------------------------------------------------------------------- *)

val mergen = ref 0
val mergedir = selfdir ^ "/merge"
fun init_merge () = (mergen := 0; clean_dir mergedir) 

fun in_defv id = id - minop >= 0 andalso id - minop < Vector.length (!defv);
fun rm_missing macro = filter (fn i => i < minop orelse in_defv i) macro

fun check_file file =
  let
    val _ = print_endline file 
    val dir = OS.Path.dir (OS.Path.dir file)
    val _ = read_def (dir ^ "/defold")
    val _ = print_endline (its (Vector.length (!defv)) ^ " definitions")
    val candl = map (rm_missing o compress_all_idl) (read_cand file)
    val _ = print_endline (its (length candl) ^ " candidates")
    val candle = map (unfold_def (!defv)) candl
    val candlp = extract_candl candle
  in
    check_candl candlp
  end

val checkspec : (unit, string, (anum * (int * cand) list) list) extspec =
  {
  self_dir = selfdir,
  self = "def.checkspec",
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
  write_result = write_itcandl,
  read_result = let fun f file = 
    (cmd_in_dir selfdir ("cp " ^ file ^ " " ^ mergedir ^ "/" ^ its (!mergen)); 
     incr mergen; [])
    in f end
    }

fun stats_sol file itsol =
  let
    val freqd = ref (dempty Int.compare)
    fun count_id m = 
      let 
        val m' = compress_all_idl m 
        val idl = filter (fn x => x >= minop) m'
      in
        freqd := count_dict (!freqd) idl
      end
    fun string_of_tp (t,(p,(n,m))) =
      (
      count_id m;
      "size: " ^ its n ^ 
      ", time: " ^ its t ^ 
      ", prog: " ^ gpt_of_prog p ^ 
      ", macro: " ^ string_of_macro m
      )
    fun string_of_itprog (i,tpl) = 
      "https://oeis.org/" ^ "A" ^ its i ^ " : " ^ 
      string_of_seq (valOf (Array.sub (oseq,i))) ^ "\n" ^ 
      String.concatWith "\n" (map string_of_tp tpl)
    val itsolsort = dict_sort 
      (snd_compare (list_compare (snd_compare cand_compare_size))) itsol
    val _ = writel file (map string_of_itprog itsolsort)
    fun f (id,n) = 
      its n ^ ": " ^ string_of_macro (expand_id id) ^ ", " ^ 
      string_of_macro (Vector.sub (!defv, id - minop))
    val l = dict_sort compare_imax (dlist (!freqd))
  in
    writel (file ^ "_deffreq") (map f l) 
  end
  
fun stats_dir dir oldsol newsol =
  let
    fun log s = (print_endline s; append_endline (dir ^ "/log") s)
    val oldset = enew Int.compare (map fst oldsol);
    val diff = filter (fn x => not (emem (fst x) oldset)) newsol    
  in
    log ("sol+oldsol: " ^ its (length newsol));
    stats_sol (dir ^ "/stats_sol") newsol;
    log ("diff: " ^ its (length diff));
    stats_sol (dir ^ "/stats_diff") diff
  end

val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)

(* -------------------------------------------------------------------------
   Parallel check: merging solutions
   ------------------------------------------------------------------------- *)

fun merge_itsol_file d file =
  let val itsol = read_itcandl file in
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
    val _ = if not (exists_file oldsolfile) then ()
            else merge_itsol_file d oldsolfile
  in
    dlist (!d)
  end

fun write_gptsol file sol =
  let
    fun f (i,tpl) =
      let 
        val seqs = gpt_of_seq (rev (first_n 16 (valOf (Array.sub (oseq,i))))) 
        fun g (t,(p,(n,macro))) = macro
        val macrol = map g tpl
        fun h macro =
          seqs ^ ">" ^ string_of_macro 
            (if !reverse_flag then rev macro else macro)
      in
        map h macrol
      end
    val l1 = List.concat (map f sol)
    val _ = print_endline ("write_gptsol: " ^ its (length l1))
  in
    writel file l1
  end

fun mkdir_exp expname = 
  (
  mkDir_err (selfdir ^ "/exp");
  mkDir_err (selfdir ^ "/exp/" ^ expname)
  )

fun progl_of_sol sol = 
  mk_fast_set prog_compare (map (fst o snd) (List.concat (map snd sol)))

fun parallel_check_def expname = 
  let 
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkdir_exp expname
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val splitdir = dir ^ "/split"
    val _ = mkDir_err splitdir
    val _ = cmd_in_dir dir "split -l 10000 cand split/cand"
    val filel = map (fn x => splitdir ^ "/" ^ x) (listDir splitdir) 
    fun log s = (print_endline s; append_endline (dir ^ "/log") s)
    val _ = read_def (dir ^ "/defold")
    val _ = log ("reading " ^ its (Vector.length (!defv)) ^ " definitions")
    val _ = init_merge ()
    val (_,t) = add_time (parmap_queue_extern ncore checkspec ()) filel
    val _ = log ("checking time: " ^ rts_round 6 t)
    val (tempsol,t) = add_time merge_itsol_default dir
    val _ = log ("merging time: " ^ rts_round 6 t)
    val _ = init_merge ()
    val (_,t) = add_time (mk_def 10) (progl_of_sol tempsol)
    val _ = log ("mk_def time: " ^ rts_round 6 t)  
    val (newsol,t) = add_time recompute_macro tempsol
    val _ = log ("recompute_macro time: " ^ rts_round 6 t)
    val newdeffile = dir ^ "/" ^ "defnew"
    val newsolfile = dir ^ "/" ^ "solnew"
    val gptfile = dir ^ "/" ^ "solnewgpt" 
    val oldsol = 
      if not (exists_file (dir ^ "/" ^ "solold")) 
      then [] 
      else read_itcandl (dir ^ "/" ^ "solold")
  in
    stats_dir dir oldsol newsol;
    write_def (newdeffile ^ "_temp");
    write_gptsol (gptfile ^ "_temp") newsol;
    write_itcandl (newsolfile ^ "_temp") newsol;
    OS.FileSys.rename {old = newdeffile ^ "_temp", new = newdeffile};
    OS.FileSys.rename {old = newsolfile ^ "_temp", new = newsolfile};
    OS.FileSys.rename {old = gptfile ^ "_temp", new = gptfile}
  end

(* -------------------------------------------------------------------------
   Create initial files
   ------------------------------------------------------------------------- *)

fun itcand_of_itprog (i,tpl) =
  let fun f (t,p) = 
    let val m = macro_of_prog p in
      (t,(p,(length m,m)))
    end
  in
    (i, map f tpl)
  end
  
fun convertto_itcandl filein fileout = 
  let val sol = read_itprogl filein in
    write_itcandl fileout (map itcand_of_itprog sol)    
  end

fun init_itcand dir n itcandl =
  let 
    val _ = mkDir_err dir
    val newdeffile = dir ^ "/" ^ "defnew"
    val newsolfile = dir ^ "/" ^ "solnew"
    val gptfile = dir ^ "/" ^ "solnewgpt"  
    val _ = defv := Vector.fromList []
    val (_,t) = add_time (mk_def n) (progl_of_sol itcandl)
    val _ = print_endline ("mk_def time: " ^ rts_round 6 t)  
    val (newsol,t) = add_time recompute_macro itcandl
  in
    write_def newdeffile;
    write_gptsol gptfile newsol;
    write_itcandl newsolfile newsol
  end
       
fun init_itprog dir n itprogl =
  init_itcand dir n (map itcand_of_itprog itprogl)



end (* struct *)  


(*
PolyML.print_depth 20;
load "def"; open aiLib kernel def;

gen_cand 1000;
gen_def 123;

read_def "exp/def3/defold";
Vector.length (!defv);
val candl = read_cand "exp/def3/cand";
val candl1 = map compress_all_idl candl;
val l = filter contain_id candl1;
val candle = map expand candl;
val candlp = extract_candl candle;
*)


(* Create initial files
load "def"; open aiLib kernel def;

init_itprog (selfdir ^ "/initgreedy") 20 (read_itprogl "sol0");
init_itprog (selfdir ^ "/initgreedy") 20 (read_itcandl "solnew");
*)


