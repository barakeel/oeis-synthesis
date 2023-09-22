structure ramsey :> ramsey =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty rconfig satenc 
smlParallel
val ERR = mk_HOL_ERR "ramsey"

 
 (* -------------------------------------------------------------------------
   Importing 3,5 and 4,4 graphs (precomputed)
   ------------------------------------------------------------------------- *) 

val infts = IntInf.toString
val stinf = valOf o IntInf.fromString

fun read35 csize = map stinf
  (readl (selfdir ^ "/ramsey_3_5/" ^ its csize))
fun read44 dsize = map stinf
  (readl (selfdir ^ "/ramsey_4_4/" ^ its dsize)) 

fun read35gen csize = map stinf
  (readl (selfdir ^ "/ramsey_3_5_gen/" ^ its csize))
fun read44gen dsize = map stinf
  (readl (selfdir ^ "/ramsey_4_4_gen/" ^ its dsize)) 

(* -------------------------------------------------------------------------
   Generalization
   ------------------------------------------------------------------------- *) 

fun all_parents mat = 
  let
    val size = mat_size mat
    val l = ref []
    fun f (i,j,x) =
      if i >= j orelse x = 0 then () else 
      let 
        val newm = mat_copy mat
        val _ = mat_update_sym (newm,i,j,0)
        val normm = normalize_nauty newm
      in 
        l := normm :: !l
      end
  in
    mat_appi f mat; mk_fast_set mat_compare (!l)
  end;

fun all_leafs mat =
  let
    val size = mat_size mat
    val l = ref []
    fun f (i,j,x) =
      if i >= j orelse x <> 0 then () else 
      l := [((i,j),1),((i,j),2)] :: !l
    val newl = (mat_appi f mat; !l)
    val edgecll = cartesian_productl newl
    fun g edgecl = 
      let 
        val newm = mat_copy mat
        fun h ((i,j),c) = mat_update_sym (newm,i,j,c) 
      in
        app h edgecl; normalize_nauty newm
      end
    val childl = map g edgecll
  in
    mk_fast_set mat_compare childl
  end;

fun all_children mat =
  let
    val size = mat_size mat
    val l = ref []
    fun f (i,j,x) =
      if i >= j orelse x <> 0 then () else 
        l := ((i,j),1) :: ((i,j),2) :: !l
    val edgecl = (mat_appi f mat; !l)
    fun g ((i,j),c) = 
      let 
        val newm = mat_copy mat
        val _  = mat_update_sym (newm,i,j,c) 
      in
        normalize_nauty newm
      end
    val childl = map g edgecl
  in
    mk_fast_set mat_compare childl
  end;   
   
     
fun next_gen leafd l = 
  let  
    val l1 = mk_fast_set mat_compare (List.concat (map all_parents l))
    fun is_fullanc m = all (fn x => emem x leafd) (all_leafs m)
    val l2 = filter is_fullanc l1;
  in
    l2
  end;

fun loop_next_gen ngen leafd l result =
  let
    val (nextl,t) = add_time (next_gen leafd) l
    val _ = print_endline (its (ngen+1) ^ ": " ^ 
      its (length nextl) ^ " in " ^ rts_round 4 t ^ " seconds")
  in
    if null nextl then rev result else 
    loop_next_gen (ngen + 1) leafd nextl (l :: result)
  end;
  
fun generalize leafd leaf = 
  loop_next_gen 0 leafd [leaf] []


(* -------------------------------------------------------------------------
   Cover using mutiple generalizations
   ------------------------------------------------------------------------- *)

fun cover_score coverd mp =
  length (filter (fn x => not (emem x coverd)) (all_leafs mp))

fun find_best_mpl coverd mpl =
  let val l = 
    dict_sort compare_imax (map_assoc (cover_score coverd) mpl)
  in
    hd l
  end

fun find_best_mpll coverd mpll = 
  let 
    val l1 = map (find_best_mpl coverd) mpll 
    val l2 = map_snd (fn x => ~x) l1
    val l3 = number_snd 0 l2
    val l4 = map (fn ((a,b),c) => (a,(b,c))) l3
    val cmp = snd_compare (cpl_compare Int.compare Int.compare)
  in
    hd (dict_sort cmp l4)
  end  
  
fun loop_cover leafs leafd coverd uncover result =
  if null uncover then rev result else
  let 
    val m0 = random_elem uncover
    val (mpll,t1) = add_time (generalize leafd) m0
    val ((mp,(sc,depth)),t2) = add_time (find_best_mpll coverd) mpll
    val mcover = filter (fn x => not (emem x coverd)) (all_leafs mp) 
    val mcoverd = enew mat_compare mcover
    val newcoverd = eaddl mcover coverd
    val newuncover = filter (fn x => not (emem x mcoverd)) uncover
    val _ = print_endline (
      "Covering " ^ its (~sc) ^ " graphs (" ^ 
      its (length newuncover) ^ " remaining)" ^
      " at depth " ^ its (length mpll - 1) ^ "," ^ its depth ^ 
      " in " ^ rts_round 4 t1 ^ " seconds and in " ^ 
      rts_round 4 t2 ^ " seconds")
  in  
    loop_cover leafs leafd newcoverd newuncover ((mp,mcover) :: result)
  end;
  
fun compute_cover leafs = 
  let val leafd = enew mat_compare leafs in 
    loop_cover leafs leafd (eempty mat_compare) leafs [] 
  end
  
(* -------------------------------------------------------------------------
   Parallel generalization and cover
   ------------------------------------------------------------------------- *)

(* 

fun mat_depth m =
  let 
    val counter = ref 0 
    fun f (i,j,x) = if i >= j orelse x <> 0 then () else incr counter
  in
    mat_appi f m; !counter
  end
   
fun write_mat file m = writel file [szip_mat m] 
fun read_mat file = sunzip_mat (singleton_of_list (readl file)) 

fun write_matl file ml = writel file (map szip_mat ml)
fun read_matl file = map sunzip_mat (readl file)
  
val coverspec : (mat list, mat, mat list) extspec =
  {
  self_dir = selfdir,
  self = "ramsey.coverspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = generalize2,
  write_param = write_matl,
  read_param = read_matl,
  write_arg = write_mat,
  read_arg = read_mat,
  write_result = write_matl,
  read_result = read_matl
  }

fun covscore coverd mp =
  (~ (length (filter (fn x => not (emem x coverd)) (all_leafs mp))),
   mat_depth mp)

fun best_mpl coverd mpl =
  let 
    val cmp = snd_compare (cpl_compare Int.compare Int.compare)
    val l = dict_sort cmp (map_assoc (covscore coverd) mpl)
  in
    fst (hd l)
  end
  
fun add_mpl (mpl,(coverd,uncover,result)) =
  let
    val mp = best_mpl coverd mpl
    val mcover = filter (fn x => not (emem x coverd)) (all_leafs mp) 
    val mcoverd = enew mat_compare mcover
    val newcoverd = eaddl mcover coverd
    val newuncover = filter (fn x => not (emem x mcoverd)) uncover
    val newresult = (mp,mcover) :: result
  in
    (newcoverd,newuncover,newresult)
  end
  
fun loop_cover_parallel ncore leafs (coverd,uncover,result) =
  if null uncover then rev result else
  let 
    val ml = random_subset 4 uncover
    val param = leafs
    val ncore' = Int.min (ncore, length ml)
    val (mpll,t1) = add_time (parmap_queue_extern ncore' coverspec param) ml
    val _ = log ("Parallel cover in " ^ rts_round 4 t1 ^ " seconds")
    val ((newcoverd,newuncover,newresult),t2) = 
      add_time (foldl add_mpl (coverd,uncover,result)) mpll
    val _ = log (its (elength newcoverd) ^ " covered in " ^
         rts_round 4 t2 ^ " seconds")
  in  
    loop_cover_parallel ncore leafs (newcoverd,newuncover,newresult)
  end; 
  
fun loop_cover_para expname ncore leafs =
  let
    val expdir = selfdir ^ "/exp/" ^ expname
    val _ = app mkDir_err [selfdir ^ "/exp", expdir]
    val _ = smlExecScripts.buildheap_dir := expdir
    val _ = store_log := true
    val _ = logfile := expdir ^ "/log"
  in
    loop_cover_parallel ncore leafs (eempty mat_compare,leafs,[])
  end

*)

(* -------------------------------------------------------------------------
   Glueing pairs using Cadical
   ------------------------------------------------------------------------- *)

fun glue buildheapdir (ci,di)  = 
  let
    val dir = OS.Path.dir buildheapdir ^ "/sat"
    val file = dir ^ "/r45_10-14"
    val (ce,de) = (unzip_mat ci, unzip_mat di)
    val pbid = szip_mat ce ^ "-" ^ szip_mat de
    val _ = write_assignl file (read_mapping file) pbid (ce,de);
    val fileclauses = file ^ "_clauses"
    val fileassign = file ^ "_assign_" ^ pbid
    val filein = file ^ "_in_" ^ pbid
    val fileout = filein ^ "_result"
    val _ = cmd_in_dir dir 
      ("cat " ^ fileassign ^ " " ^ fileclauses ^ " > " ^ filein)
    val (_,t2) = add_time (cmd_in_dir dir) ("sh cadical.sh " ^ filein)
    val sl = readl fileout
    val r = mem "UNSATISFIABLE" (String.tokens Char.isSpace (hd sl))
    val sats = if r then "unsat" else ("sat " ^ hd (tl sl))
  in
    app remove_file [fileassign,filein,fileout];
    print_endline (String.concatWith " "
      [IntInf.toString ci, IntInf.toString di, sats, rts_round 4 t2]);
    r
  end

(* -------------------------------------------------------------------------
   R(4,5) parallel execution
   ------------------------------------------------------------------------- *)

fun ramseyspec_fun () (m1,m2) = 
  glue (!smlExecScripts.buildheap_dir) (m1,m2)

fun write_matpair file (m1,m2) = writel file (map IntInf.toString [m1,m2])
fun read_matpair file = 
  pair_of_list (map (valOf o IntInf.fromString) (readl file)) 
fun write_bool file b = writel file [bts b]
fun read_bool file = string_to_bool (singleton_of_list (readl file))


val ramseyspec : (unit, IntInf.int * IntInf.int, bool) extspec =
  {
  self_dir = selfdir,
  self = "ramsey.ramseyspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] ^ ")"),
  function = ramseyspec_fun,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_matpair,
  read_arg = read_matpair,
  write_result = write_bool,
  read_result = read_bool
  }

fun r45 ncore expname csize dsize =
  let
    val expdir = selfdir ^ "/exp/" ^ expname
    val buildheapdir = expdir ^ "/buildheap"
    val satdir = expdir ^ "/sat"
    val _ = app mkDir_err [selfdir ^ "/exp",expdir,satdir,buildheapdir]
    val _ = write_pb_10_14 (satdir ^ "/r45_10-14");
    val _ = cmd_in_dir selfdir ("cp cadical.sh " ^ satdir)
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle 
       NotFound => 10000) 
    val _ = smlExecScripts.buildheap_dir := buildheapdir
    val (cl,dl) = (read35gen csize, read44gen dsize)
    val mml = cartesian_product cl dl
    val ncore' = Int.min (ncore,length mml)
    val (bl,t) = add_time (parmap_queue_extern ncore' ramseyspec ()) mml 
  in
    if all I bl then log "UNSATISIFABLE" else log "SATISIFABLE"
  end

  
end (* struct *)

(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey graph;
PolyML.print_depth 10;

val csize = 10;
val l = read35 csize; 
val gen0 =  map (unzip_full csize) l;
val (mp,cover) = split (compute_cover gen0);
val mpdesc = enew mat_compare (List.concat (map all_leafs mp));
all (fn x => emem x mpdesc) gen0;
mkDir_err "ramsey_3_5_gen";
writel ("ramsey_3_5_gen/" ^ its csize) (map szip_mat mp);
writel "r45_cover35_10_stats" (map (its o length) cover);
*)


(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;

r45 100 (selfdir ^ "exp/r45_3-5-10" 10 14;

*)


