structure def :> def =
struct

open HolKernel Abbrev boolLib aiLib kernel exec bloom smlParallel

val ERR = mk_HOL_ERR "def"
type macro = int list
type cand = prog * (int * macro)

(* -------------------------------------------------------------------------
   Extra tokens for definitions
   ------------------------------------------------------------------------- *) 

val minop = Vector.length operv
val maxop = minop + 9
fun is_id x = x >= minop
fun index_id x = x - minop

(* -------------------------------------------------------------------------
   Read definitions and candidates
   ------------------------------------------------------------------------- *)

val reverse_flag = ref true

fun macro_of_string s = map id_of_gpt (String.tokens Char.isSpace s)
fun string_of_macro il = String.concatWith " " (map gpt_of_id il)

val defv = ref (Vector.fromList [])
fun read_def file = defv := 
  Vector.fromList (map_assoc length (map macro_of_string (readl file)))
 
fun read_cand file =
  let val macrol = map macro_of_string (readl file) in
    if !reverse_flag then map rev macrol else macrol  
  end

(* -------------------------------------------------------------------------
   Generate random candidates and random definitions for testing
   ------------------------------------------------------------------------- *) 

fun random_cand () = (if !reverse_flag then rev else I)
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
   Converting list of indices to a single index
   ------------------------------------------------------------------------- *)

fun compress_idl idl =
  let fun loop acc lcur = 
    case lcur of [] => acc | a :: m => loop (10 * acc + a) m
  in
    minop + loop 0 (rev (map index_id idl))
  end

fun lfields_aux buf acc l = case l of
    [] => rev (rev buf :: acc)
  | a :: m => 
    if null buf orelse is_id (hd buf) = is_id a 
    then lfields_aux (a :: buf) acc m
    else lfields_aux [a] (rev buf :: acc) m

fun lfields l = lfields_aux [] [] l;

fun in_defv id =
  id - minop >= 0 andalso id - minop < Vector.length (!defv);

(* does some cleaning too if a id does not exists *)
fun compress_all_id macro =
  let 
    fun f idl = 
      if not (is_id (hd idl)) then idl else
      let val i = compress_idl idl in
        if in_defv i then [i] else []
      end
  in
    List.concat (map f (lfields macro))
  end

fun expand_id_aux x =
  if x < 10 then [x] else (x mod 10) :: expand_id_aux (x div 10)

fun expand_id x = 
  map (fn y => y + minop) (expand_id_aux (x - minop)) 

fun expand_all_id macro = 
  let fun f i = if is_id i then expand_id i else [i] in
    List.concat (map f macro)
  end

(* -------------------------------------------------------------------------
   Expand and compress definitions
   ------------------------------------------------------------------------- *)
 
fun expand_aux d i acc macro = case macro of
    [] => (d,rev acc)
  | a :: m => 
    if not (is_id a) then expand_aux d (i + 1) (a :: acc) m else 
    let 
      val (def,size) = Vector.sub (!defv, a - minop) 
      val newd = dadd i (a,size) d
    in
      expand_aux newd (i + size) (rev def @ acc) m
    end

fun expand macro = expand_aux (dempty Int.compare) 0 [] macro

fun compress_aux acc (d,macro) = case macro of 
    [] => rev acc
  | (a,i) :: m => 
   (
   case dfindo i d of 
     NONE => compress_aux (a :: acc) (d,m)
   | SOME (macroid,size) =>
     let val (l1,l2) = part_n size macro in
       if length l1 < size 
       then compress_aux (a :: acc) (d,m)
       else compress_aux (macroid :: acc) (d,l2)  
     end
   )
  
fun compress_indexed (d,macro) = compress_aux [] (d,macro)    
fun compress (d,macro) = compress_indexed (d, number_snd 0 macro) 


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
fun  macro_of_prog p = rev (macro_of_prog_aux p);

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
  
fun collect_aux moveltop = 
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
     loop [] moveltop; !progl
   end;

fun subseq (n,m) l = first_n (m-n+1) (snd (part_n n l))

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

fun collect progd (d,macro) =
  let
    val macroi = number_snd 0 macro
    val progiil = collect_aux (number_snd 0 macro)
    fun f (p,a,b) = 
      let 
        val macro1 = compress_indexed (d, subseq (a,b) macroi) 
        val macro2 = expand_all_id macro1  
      in
        (p, (length macro2, macro1))
      end
    val candl = map f progiil
  in
    update_progd progd candl 
  end
  
fun extract_candl candle = 
  let
    val progd = ref (dempty prog_compare)
    val (_,t) = add_time (app (collect progd)) candle
    val _ = print_endline ("extract_candl: " ^ rts_round 2 t)
    val _ = print_endline ("cand: " ^ its (dlength (!progd)))
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
   Turn programs into definitions
   ------------------------------------------------------------------------- *)

fun all_suffix l = case l of [] => [] | a :: m => l :: all_suffix m;
fun all_revprefix l = all_suffix (rev l);

fun mk_def limit progl = 
  let
    val defsize = length (expand_id (Vector.length (!defv) + minop))
    val prevd = enew (list_compare Int.compare) 
      (map (rev o fst) (vector_to_list (!defv)))
    val macrol = map macro_of_prog progl
    val subd = ref (dempty (list_compare Int.compare))
    fun f_one macro = 
      let val l = all_revprefix (first_n 240 macro) in
        subd := count_dict (!subd) l
      end
    fun f macro = case macro of [] => () | a :: m => (f_one macro; f m)
    val _ = app f macrol
    val l1 = filter (fn (a,b) => b >= 20 andalso length a > defsize) 
      (dlist (!subd))
    fun score (il,freq) = if emem il prevd then NONE 
       else SOME (il, (length il - defsize) * freq)
    val l2 = List.mapPartial score l1
    val l3 = first_n limit (dict_sort compare_imax l2)
  in
    map (fn (a,b) => rev a) l3  
  end;


(* 
PolyML.print_depth 20;
load "def"; open aiLib kernel def;

val sol = read_itprogl "sol0";
val progl1 = map snd (List.concat (map snd sol));
val progl2 = mk_fast_set prog_compare progl1;
val defl = mk_def 10 progl2;
writel "def0" (map string_of_macro defl);
*)

fun replace_aux n (def,id) macro = 
  case macro of [] => [] | a :: m =>
  let val (l1,l2) = part_n n macro in
    if l1 = def 
    then id :: replace_aux n (def,id) l2
    else a :: replace_aux n (def,id) m
  end

fun replace (def,id) macro = replace_aux (length def) (def,id) macro;
  
fun replacenew macro (def,id) = 
  let val newmacro = replace (def,id) macro in
    if newmacro = macro then NONE else SOME macro
  end
  
fun replacenewl defidl p =
  let val macro = macro_of_prog p in
    List.mapPartial (replacenew macro) defidl
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

fun check_file file =
  let
    val candl = map compress_all_id (read_cand file)
    val _ = print_endline (file ^ ":" ^ its (length candl))
    val candle = map expand candl
    val candlp = extract_candl candle
  in
    check_candl candlp
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
    fun string_of_tp (t,p) =
      "size: " ^ its (fst (snd p)) ^ 
      ", time: " ^ its t ^ 
      ", prog: " ^ gpt_of_prog (fst p) ^ 
      ", macro: " ^ string_of_macro (snd (snd p))
    fun string_of_itprog (i,tpl) = 
      "https://oeis.org/" ^ "A" ^ its i ^ " : " ^ 
      string_of_seq (valOf (Array.sub (oseq,i))) ^ "\n" ^ 
      String.concatWith "\n" (map string_of_tp tpl)
    val itsolsort = dict_sort 
      (snd_compare (list_compare (snd_compare cand_compare_size))) itsol
    fun f (macro,n) = its n ^ ": " ^ string_of_macro macro
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

fun write_gptsol defidl file sol =
  let
    fun f (i,tpl) =
      let 
        val seqs = gpt_of_seq (rev (first_n 16 (valOf (Array.sub (oseq,i))))) 
        fun g1 (t,(p,(n,macro))) = macro
        fun g2 (t,(p,(n,macro))) = p
        val macrol = map g1 tpl
        val pl = map g2 tpl
        val extral = List.concat (map (replacenewl defidl) pl)
        fun h macro =
          let val macro' = expand_all_id macro in
            seqs ^ ">" ^ string_of_macro 
              (if !reverse_flag then rev macro' else macro')
          end
      in
        map h (macrol @ extral)
      end
  
  in
    writel file (shuffle (List.concat (map f sol)))
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
    val (newsol,t) = add_time merge_itsol_default dir
    val _ = log ("merging time: " ^ rts_round 6 t)
    val _ = init_merge ()
    val (defl,t) = add_time (mk_def 10) (progl_of_sol newsol)
    val newdefl = map fst (vector_to_list (!defv)) @ defl
    val defidl = number_snd (Vector.length (!defv)) defl
    val _ = log ("definition time: " ^ rts_round 6 t) 
    val newdeffile = dir ^ "/" ^ "defnew"
    val newsolfile = dir ^ "/" ^ "solnew"
    val gptfile = dir ^ "/" ^ "solnewgpt" 
    val oldsol = 
       if not (exists_file (dir ^ "/" ^ "solold")) 
       then [] 
       else read_itcandl (dir ^ "/" ^ "solold")
  in
    stats_dir dir oldsol newsol;
    writel (newdeffile ^ "_temp") (map string_of_macro newdefl);
    write_gptsol defidl (gptfile ^ "_temp") newsol;
    write_itcandl (newsolfile ^ "_temp") newsol;
    OS.FileSys.rename {old = newdeffile ^ "_temp", new = newdeffile};
    OS.FileSys.rename {old = newsolfile ^ "_temp", new = newsolfile};
    OS.FileSys.rename {old = gptfile ^ "_temp", new = gptfile}
  end

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


end (* struct *)  


(*
PolyML.print_depth 20;
load "def"; open aiLib kernel def;

gen_cand 1000;
gen_def 123;

read_def "def";
val candl = map parse (read_cand "cand");
val candle = map expand candl;
val candlp = extract_candl candle;

convertto_itcandl "exp/def/solold_prog" "exp/def/soldold_cand";
*)


