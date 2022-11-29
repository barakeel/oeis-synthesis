structure def :> def =
struct

open HolKernel Abbrev boolLib aiLib kernel exec bloom smlParallel

val ERR = mk_HOL_ERR "def"
type macro = int list

fun macro_of_string s = map id_of_gpt (String.tokens Char.isSpace s)
fun string_of_macro il = String.concatWith " " (map gpt_of_id il)

type cand = prog * (int * macro);

(* stop token could be added after maxop + 1 *)
(* val defv = Vector.fromList (map macro_of_string readl (selfdir ^ "/def")) *)
(* remove undefined def + remove leading zeros *)
fun rm_undef (macro,i) = filter (fn x => x < minop + i) macro;

(* -------------------------------------------------------------------------
   Separate definitions from the rest and cleaning up definitions
   ------------------------------------------------------------------------- *)

load "kernel"; open kernel aiLib;
PolyML.print_depth 10;
val minop = Vector.length operv;
val maxop = minop + 9;
fun is_defid x = x >= minop andalso x <= maxop;
fun index_defid x = x - minop;

fun lfields_aux buf acc l = case l of
    [] => rev (rev buf :: acc)
  | a :: m => 
    if null buf orelse is_defid (hd buf) = is_defid a 
    then lfields_aux (a :: buf) acc m
    else lfields_aux [a] (rev buf :: acc) m

fun lfields l = lfields_aux [] [] l;

fun random_defbody x = List.tabulate (x, fn _ => random_int (0,maxop));  
    
fun index_defcode defcode =
  let fun loop acc lcur = 
    case lcur of [] => acc | a :: m => loop (10 * acc + a) m
  in
    loop 0 (rev (map index_defid defcode))
  end;
  
fun defcode_index x = 
  if x < 10 then [minop + x] else 
  minop + (x mod 10) :: defcode_index (x div 10)
 
val body = random_defbody 10;     
fun is_defined index = index < 2003;

fun cleanup defbody =   
  let 
    fun f defcode = if not (is_defid (hd defcode)) then defcode else
      let val i = index_defcode defcode in
        if is_defined i then [minop + i] else []
      end
  in
    List.concat (map f defbody)
  end

val defbody = lfields (random_defbody 20);
val defbody2 = cleanup defbody;

(* -------------------------------------------------------------------------
   Discover new definitions
   ------------------------------------------------------------------------- *)

(* 
takes the 10,000 most common definitions 
expanded form
*)
fun all_suffix l = case l of [] => [] | a :: m => l :: all_suffix m;
fun all_prefix l = map rev (all_suffix (rev l));
val subd = ref (dempty (list_compare Int.compare))

fun extract_subseq_one expbody = 
  let val l = all_prefix (first_n 240 expbody) in
    subd := count_dict (!subd) l
  end;

fun extract_subseq expbody = case expbody of [] => () | a :: m =>
  (extract_subseq_one expbody; extract_subseq m);
  
val expbody = random_defbody 1000; 
val _ = (subd := dempty (list_compare Intfun compression_score (il,freq) = 
  let val n = length il in (n - 3) * freq end;
  
val l = map_assoc compression_score (dlist (!subd));  
dict_sort compare_imax l;.compare); extract_subseq expbody);
!subd;
dict_sort compare_imax (dlist (!subd));

fun compression_score defsize (il,freq) = 
  let val n = length il in (n - defsize) * freq end;
  
val l = map_assoc (compression_score 1) (dlist (!subd));  
dict_sort compare_imax l;

(* -------------------------------------------------------------------------
   Storing expanded definitions in a vector
   ------------------------------------------------------------------------- *)

(* look up what I did before (max arity 2 is enough?) *)


(* -------------------------------------------------------------------------
   Expand definitions
   ------------------------------------------------------------------------- *)

  
(* -------------------------------------------------------------------------
   Collect programs from a macro in a context
   ------------------------------------------------------------------------- *)

fun next_board (board : (prog * int * int) list) (move,moven) =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 < arity
    then []   
    else (Ins (move, rev (map #1 l1)), 
          list_imin (moven :: map #2 l1), moven) :: l2
  end;

fun collect_prog_line moveltop = 
  let 
    val progl = ref []
    fun loop board movel = case movel of [] => () | (move,moven) :: m => 
      let 
        val newboard = next_board board (move,moven)
        val _ = if null newboard then () else progl := hd newboard :: !progl
      in
        loop newboard m
      end
   in
     loop [] moveltop;
     !progl
   end;

fun rename_macro macro =
  let 
    val i = ref minop
    fun f x = if is_macroid x then (incr i; !i - 1) else x
    val v = Vector.tabulate (maxop, f)
    fun g x = Vector.sub (v,x)
  in  
    map g macro
  end

fun collect_prog macro =
  let 
    val _ = macrov := empty_macrov
    val macrol1 = lfields hashop macro
    val macrol2 = map rm_undef (number_snd 0 macrol1)
    fun maxdep_of macro = 
      let val n = list_imax macro in
        if is_macroid n then index_macroid n + 1 else 0
      end
    fun depsize_of carved =
      let 
        val defl = List.tabulate (maxdep_of carved, 
          (fn x => Vector.sub (!macrov,x))) 
        val recmacro = lconcatw hashop (defl @ [carved])
      in
        recmacro
      end
    val macrol3 = map expandi (number_snd 0 macrol2)
    val progll = map collect_prog_line macrol3
    fun f (progl,orgseq) = map (fn (p,a,b) => (p, subseq (a,b) orgseq)) progl
    val l0 = combine (progll,macrol2)
    val l1 = List.concat (map f l0)
    val l2 = map_snd depsize_of l1
  in
    l2
  end

(* -------------------------------------------------------------------------
   Create a list of candidates
   ------------------------------------------------------------------------- *)

fun create_macrol (k,n,m) = 
  let
    val (macrol,t) = add_time
      List.tabulate (k, fn _ => random_macro (random_int (n,m)))
    val _ = print_endline ("create macro: " ^ rts_round 2 t)
  in
    macrol
  end
  
fun save_macrol expname macrol =
  let
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = mkDir_err dir
    val file = dir ^ "/cand"
  in
    writel file (map string_of_macro macrol)
  end  

fun merge_candl candl =
  let
    val d = ref (dempty prog_compare) 
    val cmp = cpl_compare Int.compare (list_compare Int.compare); 
    fun f (a,b) = 
      case dfindo a (!d) of
        NONE => d := dadd a b (!d)
      | SOME b' => if cmp (b,b') = LESS then d := dadd a b (!d) else ()
    val _ = app f candl
  in
    dlist (!d)
  end  
  
fun extract_candl_one macro = 
  let  
    val l1 = collect_prog macro
    fun g b = length (filter (fn x => x <> hashop) b)
    fun f (a,b) = (a,(g b, b))
    val l2 = map f l1
    val l3 = merge_candl l2
  in
    l3
  end  

fun extract_candl macrol = 
  let
    val (macroll,t) = add_time (map extract_candl_one) macrol
    val _ = print_endline ("extract_candl_one: " ^ rts_round 2 t)
    val (candl,t) = add_time merge_candl (List.concat macroll);
    val _ = print_endline ("merge_candl: " ^ rts_round 2 t)
    val _ = print_endline ("candidates: " ^ its (length candl))
  in
    candl
  end

(* -------------------------------------------------------------------------
   Test candidates (copied from check.sml)
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

val boot_flag = ref false

fun check_file file =
  let 
    val macrol = map macro_of_string (readl file)
    val macrol1 = if !boot_flag then macrol else 
      (print_endline "inverting macros"; map invert_macro macrol)
    val _ = print_endline (file ^ ":" ^ its (length macrol1))
  in
    check_candl (extract_candl macrol1)
  end

val checkspec : (unit, string, (anum * (int * cand) list) list) extspec =
  {
  self_dir = selfdir,
  self = "macro.checkspec",
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
    val d = ref (dempty (list_compare Int.compare))
    fun string_of_tp (t,p) =
      let 
        val defl = defl_macro (snd (snd p)) 
        val _ = d := count_dict (!d) defl
      in
        "size: " ^ its (fst (snd p)) ^ 
        ", time: " ^ its t ^ 
        ", prog: " ^ gpt_of_prog (fst p) ^ 
        ", macro: " ^ string_of_macro (snd (snd p))
      end
    fun string_of_itprog (i,tpl) = 
      "https://oeis.org/" ^ "A" ^ its i ^ " : " ^ 
      string_of_seq (valOf (Array.sub (oseq,i))) ^ "\n" ^ 
      String.concatWith "\n" (map string_of_tp tpl)
    val itsolsort = dict_sort 
      (snd_compare (list_compare (snd_compare cand_compare_size))) itsol
    fun f (macro,n) = its n ^ ": " ^ string_of_macro macro
    val _ = writel file (map string_of_itprog itsolsort)
    val freql = dlist (!d)
  in
    writel (file ^ "_deffreq") (map f (dict_sort compare_imax freql))
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
        fun g (t,(p,(n,macro))) = 
          seqs ^ ">" ^ string_of_macro (invert_macro macro)
      in
        map g tpl
      end
  in
    writel file (shuffle (List.concat (map f sol)))
  end

fun mkdir_exp expname = 
  (
  mkDir_err (selfdir ^ "/exp");
  mkDir_err (selfdir ^ "/exp/" ^ expname)
  )
 

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
    val _ = init_merge ()
    val (_,t) = add_time (parmap_queue_extern ncore checkspec ()) filel
    val _ = log ("checking time: " ^ rts_round 6 t)
    val (newsol,t) = add_time merge_itsol_default dir
    val _ = log ("merging time: " ^ rts_round 6 t)
    val _ = init_merge () 
    val newsolfile = dir ^ "/" ^ "solnew"
    val gptfile = dir ^ "/" ^ "solnewgpt" 
    val oldsol = 
      if not (exists_file (dir ^ "/" ^ "solold")) 
      then [] 
      else read_itcandl (dir ^ "/" ^ "solold")
  in
    stats_dir dir oldsol newsol;
    write_gptsol (gptfile ^ "_temp") newsol;
    write_itcandl (newsolfile ^ "_temp") newsol;
    OS.FileSys.rename {old = newsolfile ^ "_temp", new = newsolfile};
    OS.FileSys.rename {old = gptfile ^ "_temp", new = gptfile}
  end
    
fun boot expname ngen nmacro = 
  let 
    val _ = boot_flag := true
    val expcur = expname ^ its ngen
    val dircur = selfdir ^ "/exp/" ^ expcur
    val expnext = expname ^ its (ngen+1)
    val dirnext = selfdir ^ "/exp/" ^ expnext
    val _ = app mkdir_exp [expcur,expnext] 
    val _ = save_macrol expcur (create_macrol (nmacro,20,200))
    val _ = PolyML.fullGC ()
  in
    parallel_check_macro expcur;
    cmd_in_dir dircur ("cp " ^ dircur ^ "/solnew" ^ " " ^ dirnext ^ "/solold");
    boot expname (ngen + 1) nmacro
  end

(* -------------------------------------------------------------------------
   Beam search
   ------------------------------------------------------------------------- *)

val stopmove = maxop + 1

end (* struct *)

(* 
take a function that converts macro into terms
1,5,25
every functions

take the n most likely element after each step 
given a function that give you the probability for the next move (including the stop move).
*)

(* 
PolyML.print_depth 10;
load "macro"; open kernel aiLib macro;

val res = [0,9];
val alpha6 = rpt_fun_type 2 alpha;
fun mk_var6 s = mk_var (s,alpha6);
val nonetm = mk_var ("none",alpha);
val idtmv = Vector.fromList (map mk_var6 (List.tabulate (26,gpt_of_id)));
val ERR = mk_HOL_ERR "test";

fun term_of_macro_aux tml idl = case idl of
    [] => if null tml then raise ERR "term_of_macro" "empty" else hd tml
  | id :: idm =>
  let 
    val tmv = Vector.fromList tml
    fun f x = Vector.sub (tmv,x) handle Subscript => nonetm
    val argl = map f res
    val newtm = list_mk_comb (Vector.sub (idtmv,id), argl)
  in
    term_of_macro_aux (newtm :: tml) idm
  end;
 
fun term_of_macro macro = term_of_macro_aux [] macro; 
val macro = random_macro 10;
fun string_of_macro il = String.concatWith " " (map gpt_of_id il);
val s = string_of_macro macro;

val tm = term_of_macro macro;

*)



(*
PolyML.print_depth 10;
load "macro"; open kernel aiLib macro;

val macrol = create_macrol (10000,20,200);
val candl = extract_candl macrol;
val sol = check_candl candl;   

val macrol = create_macrol (20000,20,200);
save_macrol "macro1" macrol;
parallel_check_macro "macro1";

boot "boot3m" 0 1000000;

*)


