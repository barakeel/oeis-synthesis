structure ramsey :> ramsey =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty rconfig sat 
smlParallel
val ERR = mk_HOL_ERR "ramsey"

 
 (* -------------------------------------------------------------------------
   Importing 3,5 and 4,4 graphs (precomputed)
   ------------------------------------------------------------------------- *) 
 
fun read_case (a,b) =
  let 
    val file1 = selfdir ^ "/ramsey_3_5/" ^ its a  
    val file2 = selfdir ^ "/ramsey_4_4/" ^ its b
  in
    (Vector.fromList (readl file1), Vector.fromList (readl file2))
  end 

(* ,(10,14),(12,12),(13,11) *)
  
fun import_subgraphs () =
  let 
    val cases = [(7,17),(8,16),(9,15)]
    val l0 = map_assoc read_case cases;
    fun f (_,(a,b)) = (Vector.length a, Vector.length b)
  in
    map_assoc f l0
  end
 
val infts = IntInf.toString
val stinf = valOf o IntInf.fromString
 fun read35 csize = map stinf
  (readl (selfdir ^ "/ramsey_3_5/" ^ its csize))
fun read44 dsize = map stinf
  (readl (selfdir ^ "/ramsey_4_4/" ^ its dsize)) 

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
      if i >= j orelse x <> 0 then () else l := [((i,j),1),((i,j),2)] :: !l
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
     
fun next_gen cd l = 
  let  
    val l1 = mk_fast_set mat_compare (List.concat (map all_parents l))
    fun is_fullanc cd m = all (fn x => emem x cd) (all_leafs m)
    val l2 = filter (is_fullanc cd) l1;
  in
    l2
  end;

fun loop_next_gen ngen cd l result =
  let
    val (nextl,t) = add_time (next_gen cd) l
    val _ = print_endline (its (ngen+1) ^ ": " ^ 
      its (length nextl) ^ " in " ^ rts_round 4 t ^ " seconds")
  in
    if null nextl then rev result else 
    loop_next_gen (ngen + 1) cd nextl (l :: result)
  end;
  
fun generalize cl leaf = 
  let val cd = enew mat_compare cl in
    loop_next_gen 0 cd [leaf] []
  end

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
  
fun loop_cover leafs coverd uncover result =
  if null uncover then rev result else
  let 
    val m0 = random_elem uncover
    val (mpll,t1) = add_time (generalize leafs) m0
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
    loop_cover leafs newcoverd newuncover ((mp,mcover) :: result)
  end;
  
fun compute_cover leafs = 
  loop_cover leafs (eempty mat_compare) leafs [];  
  
  
(* -------------------------------------------------------------------------
   R(4,5) subgraphs 
   ------------------------------------------------------------------------- *)
 
(* 
load "ramsey"; open ramsey aiLib graph rconfig kernel nauty;
val ERR = mk_HOL_ERR "test"; 
 

val l35 = read35 10;
val gen0_35 = map (unzip_full 10) l35;
val (mp35,cover35) = split (compute_cover gen0_35);
length cover35;
map length cover35;
val mp35desc = enew mat_compare (List.concat (map all_leafs mp35));
all (fn x => emem x mp35desc) gen0_35;
writel "ramsey_3_5_gen/10" (map szip_mat mp35);



val l44 = read44 14;
val gen0_44 =  map (unzip_full 14) l44;
val (mp44,cover44) = split (compute_cover gen0_44);
val mp44desc = enew mat_compare (List.concat (map all_leafs mp44));
all (fn x => emem x mp44desc) gen0_44;
writel "ramsey_4_4_gen/14" (map szip_mat mp44);
length cover44;
map length cover44;


   
loop_next_gen44 "ramsey_4_4_gen" 0 (enew mat_compare gen0) [child44];


val csize = 10;
val gen10 = readl "ramsey_3_5_gen/10";
val m35 = sunzip_mat 10 (hd gen10);
val e35 = mat_to_edgecl m35;

val dsize = 14;
val gen7 = readl "ramsey_4_4_gen/7";
val m44 = sunzip_mat 14 (hd gen7);
val e44 = mat_to_edgecl m44;
val e44shifted = map_fst (fn (a,b) => (a + csize, b + csize)) e44;

val edgecl = e35 @ e44shifted;
val edgecd = symmetrify (edgecl_to_mat_size (csize + dsize) edgecl);
open sat;
val pb = all_clauses3 (csize + dsize) (4,5) edgecd;
val allvar = mk_fast_set edge_compare (List.concat (map (map fst) pb));
val vard = dnew edge_compare (number_snd 0 allvar);
val pbrenamed = map (map_fst (fn x => dfind x vard)) pb;

write_satpb "aaatest" (dlength vard, pbrenamed);

val l35 = read35 10;
val m35 = unzip_full csize (random_elem l35);
val l44 = read44 14;
val m44 = unzip_full dsize (random_elem l44);
val e35 = mat_to_edgecl m35;
val e44 = mat_to_edgecl m44;
val e44shifted = map_fst (fn (a,b) => (a + csize, b + csize)) e44;
val edgecl = map_snd (fn x => 3 - x) (e35 @ e44shifted);

val pb = map (fn x => [x]) edgecl @ all_clauses (csize + dsize) 4 5;
val pbinst =  pb;
 
val allvar = mk_fast_set edge_compare (List.concat (map (map fst) pb));
val vard = dnew edge_compare (number_snd 0 allvar);
val pbrenamed = map (map_fst (fn x => dfind x vard)) pb;
val ivard = dnew Int.compare (map swap (dlist vard));

write_satpb "aaatest" (dlength vard, pbrenamed); 
    
val sl = readl "aaacore";
val sl2 = map (String.tokens Char.isSpace) sl;
val (sl3,sl4) = partition (fn x => length x = 2) (tl sl2);
val unitl = map (string_to_int o hd) sl3;
val unitd = enew Int.compare unitl;

val sl5 = mk_fast_set String.compare (List.concat sl4);
val litl = map string_to_int sl5;
val litl2 = filter (fn x => emem (~x) unitd) litl;


length sl3;
    
    
         
*)

(*
fun clique_of_subset (subset,color) =
  let val pairl = all_pairs (dict_sort Int.compare subset) in
    map (fn x => (pair x, color)) pairl
  end

fun all_clauses size (blueshape,redshape) = 
  let
    val bluesize = mat_size blueshape
    val bluesubsetl = subsets_of_size bluesize (List.tabulate (size,I))
    val redsize = mat_size redshape
    val redsubsetl = subsets_of_size redsize (List.tabulate (size,I))
    val subsetl = map_assoc (fn _ => blue) bluesubsetl @
                  map_assoc (fn _ => red) redsubsetl
  in
    map clique_of_subset subsetl
  end

fun clique_of_subset (subset,color) =
  let val pairl = all_pairs (dict_sort Int.compare subset) in
    map (fn x => (x, color)) pairl
  end;

fun all_clauses size bluesize redsize = 
  let
    val bluesubsetl = subsets_of_size bluesize (List.tabulate (size,I))
    val redsubsetl = subsets_of_size redsize (List.tabulate (size,I))
    val subsetl = map_assoc (fn _ => blue) bluesubsetl @
                  map_assoc (fn _ => red) redsubsetl
  in
    map clique_of_subset subsetl
  end;


*)


(* -------------------------------------------------------------------------
   R(4,5) problem creation
   ------------------------------------------------------------------------- *)
 
(* 
load "ramsey"; open ramsey aiLib graph rconfig kernel;
val ERR = mk_HOL_ERR "test";

fun all_subsets l = case l of
    [] => [[]]
  | a :: m => 
    let val r = all_subsets m in
      map (fn x => a :: x) r @ r
    end;
    
fun subsets_of_size_faster n (l,ln) = 
  if n > ln then [] else if n = ln then [l] else
  (
  case l of
    [] => if n = 0 then [[]] else []
  | a :: m => 
    let
      val l1 = map (fn subset => a::subset) 
        (subsets_of_size_faster (n - 1) (m,ln-1))
      val l2 = subsets_of_size_faster n (m,ln-1)
    in
      l1 @ l2
    end  
  )
fun subsets_of_size n l =  subsets_of_size_faster n (l, length l);    
    
fun is_triangle m l = case l of
      [a,b,c] => 
      mat_sub (m,a,b) = blue andalso
      mat_sub (m,b,c) = blue andalso
      mat_sub (m,a,c) = blue 
    | _ => raise ERR "is_triangle" "";

fun all_triangles m = 
  enew (list_compare Int.compare) (filter (is_triangle m) trianglel);

val vertexl = List.tabulate (14,I);
val conel = all_subsets vertexl;
val trianglel = subsets_of_size 3 vertexl;
val l44 = read44 14;

val i44 = random_elem l44;
val m44 = unzip_full 14 i44;
val triangled = all_triangles m44;
fun has_triangle subset = 
  exists (fn x => emem x triangled) (subsets_of_size 3 subset);
val feasibleconel = filter (not o has_triangle) conel;
length feasibleconel;

val feanl = map_assoc length feasibleconel;
val d = dregroup Int.compare (map swap feanl);
val l = dlist d;
val l2 = map_snd length l;

val l35 = read35 10;
val m35 = unzip_full 10 (random_elem l35);
val vertexl35 = List.tabulate (10,I);
fun bluedegree_of graph x = length (neighbor_of blue graph x);
val degreel = map (bluedegree_of m35) vertexl35;


val fea2l = cartesian_product feasibleconel feasibleconel;

fun complement a = filter (fn x => mem x a) vertexl;
val unconel = map complement feasibleconel;

fun inter n l1 l2 =
  case (l1,l2) of
    ([],_) => false
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => 
    if a1 = a2 then (if n >= 2 then true else inter (n+1) m1 m2)
    else if a1 < a2 then inter n m1 l2 else inter n l1 m2;

val fea2l = cartesian_product unconel unconel;

val fea2l' = filter (fn (a,b) => not (inter 0 a b)) fea2l; 
length fea2l; length fea2l';

*) 

(* -------------------------------------------------------------------------
   R(4,5) search loop
   ------------------------------------------------------------------------- *)
 
val satdir_glob = ref selfdir
val subgraphs_glob = ref []
 

fun all_subgraphs size mati = 
  let
    val mat = unzip_full size mati
    fun f x =
      let
        val l = filter (fn y => y <> x) (List.tabulate (size,I))
        val permf = mk_permf l
      in
        zip_full (normalize_nauty (mat_permute (mat,size - 1) permf))
      end
  in
    mk_fast_set IntInf.compare (List.tabulate (size,f))
  end

fun eval_pair limit csize dsize (ce,de) = 
  let
    val dir = !satdir_glob
    fun create_pb () = 
      let
        val cl = unzip_full_edgecl csize ce
        val dl = unzip_full_edgecl dsize de
        val dl' = map_fst (fn (a,b) => (a + csize, b + csize)) dl
        val edgecl = cl @ dl'
        val edgecd = symmetrify (edgecl_to_mat_size (csize + dsize) edgecl)
        val pb = all_clauses3 (csize + dsize) (4,5) edgecd @ 
                 star_clauses edgecd (12,15) csize dsize
        (* to do remove/update all_stars *)
        val allvar = mk_fast_set edge_compare (List.concat (map (map fst) pb))
        val vard = dnew edge_compare (number_snd 0 allvar) 
      in 
        (dlength vard, map (map_fst (fn x => dfind x vard)) pb)
      end
    val (newpb,t1) = add_time create_pb ()
    val file = dir ^ "/" ^ infts ce ^ "_" ^ infts de
    val fileout = file ^ "_out"
    val (_,t2) = add_time (write_satpb file) newpb
    val cmd = if limit <= 0 then "sh cadical.sh"  else
              ("sh cadical_time.sh " ^ its limit)
    val (_,t3) = add_time (cmd_in_dir dir) (cmd ^ " " ^ file)
    val sl = String.tokens Char.isSpace (hd (readl fileout))
    val r = mem "UNSATISFIABLE" sl 
    val r2 = mem "SATISFIABLE" sl
    val _ = print_endline (String.concatWith " "
      [infts ce, infts de, 
       if r then "unsat" else if r2 then "sat" else "timeout",
       rts_round 6 t1, rts_round 6 t2, rts_round 6 t3])
  in 
    remove_file file; remove_file fileout; r
  end





fun eval_pair_prevd (limit,csize,dsize) cdl = 
  map (eval_pair limit csize dsize) cdl
  
fun write_evalparam file (limit,csize,dsize) =
  writel file [its limit ^ " "  ^ its csize ^ " " ^ its dsize]
  
fun read_evalparam file =
  let 
    val sl = readl file
    val (sb,sc,sd) = triple_of_list (String.tokens Char.isSpace (hd sl))      
  in
    (string_to_int sb,string_to_int sc, string_to_int sd)
  end
  
fun write_int file i = writel file [its i]
fun read_int file = string_to_int (hd (readl file))
fun write_bool file b = writel file [bts b]
fun read_bool file = string_to_bool (hd (readl file))

fun write_infp file (a,b) = writel file (map infts [a,b])
fun read_infp file = pair_of_list (map stinf (readl file))

fun write_infpl file abl = 
  let fun f (a,b) = infts a ^ " " ^ infts b in
    writel file (map f abl)
  end
fun read_infpl file =
  let fun g s = pair_of_list (map stinf (String.tokens Char.isSpace s)) in
    map g (readl file)
  end

fun write_intl file i = writel file (map its i)
fun read_intl file = map string_to_int (readl file)
fun write_booll file b = writel file (map bts b)
fun read_booll file = map string_to_bool (readl file)


val evalspec : 
  ((int * int * int), (IntInf.int * IntInf.int) list, bool list) extspec =
  {
  self_dir = selfdir,
  self = "ramsey.evalspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir),
     "ramsey.satdir_glob := " ^  mlquote (!satdir_glob)
    ] 
    ^ ")"),
  function = eval_pair_prevd,
  write_param = write_evalparam,
  read_param = read_evalparam,
  write_arg = write_infpl,
  read_arg = read_infpl,
  write_result = write_booll,
  read_result = read_booll
  }


fun create_pairl35 prevd csize dsize cl dl =
  let
    val clsub = map_assoc (all_subgraphs csize) cl
    val l = cartesian_product clsub dl
    fun test ((c,csubl),d) =  exists (fn x => emem (x,d) prevd) csubl
    val (l1,l2) = partition test l
  in
    (map_fst fst l1, map_fst fst l2)
  end

fun create_pairl44 prevd csize dsize cl dl =
  let
    val dlsub = map_assoc (all_subgraphs dsize) dl
    val l = cartesian_product cl dlsub
    fun test (c,(d,dsubl)) = exists (fn x => emem (c,x) prevd) dsubl
    val (l1,l2) = partition test l
  in
    (map_snd fst l1, map_snd fst l2)
  end
 
fun create_pairl btest prevd csize dsize cl dl = 
  if elength prevd = 0 then ([],cartesian_product cl dl)
  else if btest 
    then create_pairl35 prevd csize dsize cl dl
    else create_pairl44 prevd csize dsize cl dl
 
fun eval_allpairs btest prevd limit csize dsize = 
  let 
    val cmp = cpl_compare IntInf.compare IntInf.compare
    val (cl,dl) = (read35 csize, read44 dsize)
    val (cn,dn) = (length cl, length dl)
    val ((pairlsub,pairl),t) = add_time 
      (create_pairl btest prevd csize dsize cl) dl
    val _ = log ""
    val _ = log (its (cn * dn) ^ " pairs (" ^ 
      its csize ^ "-" ^ its cn ^ "," ^ its dsize ^ "-" ^ its dn ^
      ") in " ^ rts_round 2 t ^ " seconds")
    val pairn = length pairl
    val pairnsub = length pairlsub
    val _ = log (its pairnsub ^ " pairs by subgraph")
  in  
    if mem csize [8,9] then (false, enew cmp pairlsub) else
    let
      val ncore' = Int.min (ncore, length pairl)
      val param = (limit,csize,dsize)
      val pairll = mk_batch_full 100 pairl
      val (bll,t) = add_time 
        (parmap_queue_extern ncore' evalspec param) pairll
      val bl = List.concat bll
      val _ = log (its pairn ^ " pairs in " ^ rts_round 2 t ^ " seconds")
      val pairlunsat = map fst (filter snd (combine (pairl,bl))) 
      val _ = log (its (length pairlunsat) ^ " pairs by cadical")
      val newd = enew cmp (pairlsub @ pairlunsat)
    in
      (all I bl, newd)
    end
  end

fun init_eval expdir (a,b) (c,d) = 
  let
    val subexpdir = expdir ^ "/" ^ 
      its a ^ "-" ^ its b ^ "_" ^ its c ^ "-" ^ its d
    val satdir = subexpdir ^ "/sat"
    val buildheapdir = subexpdir ^ "/buildheap"
    val _ = satdir_glob := satdir
    val _ = smlExecScripts.buildheap_dir := buildheapdir
    val _ = app mkDir_err [expdir,subexpdir,satdir,buildheapdir]
    val _ = store_log := true
    val _ = logfile := subexpdir ^ "/log"
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle 
       NotFound => 10000) 
  in
    cmd_in_dir selfdir ("cp cadical.sh " ^ satdir);
    cmd_in_dir selfdir ("cp cadical_time.sh " ^ satdir)
  end


(* -------------------------------------------------------------------------
   Search loop: 3,5
   ------------------------------------------------------------------------- *)

fun eval_loop35_aux expdir prevd (csize,maxcsize) dsize =      
  let 
    val _ = init_eval expdir (csize,maxcsize) (dsize,dsize)
    val limit = if csize = maxcsize then 0 else 100 
    val (alltrue,newd) = eval_allpairs true prevd limit csize dsize 
  in
    if not alltrue andalso csize = maxcsize 
      then log ("satisfiable: " ^ its csize ^ "," ^ its dsize)
    else if alltrue 
      then log ("unsatisfiable: " ^ its csize ^ "," ^ its dsize)
    else eval_loop35_aux expdir newd (csize + 1,maxcsize) dsize
  end 
  
fun eval_loop35 expdir (csize,maxcsize) dsize =
  let 
    val cmp = cpl_compare IntInf.compare IntInf.compare 
    val (_,t) =  add_time 
      (eval_loop35_aux expdir (eempty cmp) (csize,maxcsize)) dsize
  in
    log ("total time: " ^ rts_round 2 t ^ "\n")
  end
 
(* -------------------------------------------------------------------------
   Search loop: 4,4
   ------------------------------------------------------------------------- *)
    
fun eval_loop44_aux expdir prevd csize (dsize,maxdsize) =      
  let    
    val _ = init_eval expdir (csize,csize) (dsize,maxdsize)
    val limit = if dsize = maxdsize then 0 else 100 
    val (alltrue,newd) = eval_allpairs false prevd limit csize dsize 
  in
    if not alltrue andalso dsize = maxdsize 
      then log ("satisfiable: " ^ its csize ^ "," ^ its dsize)
    else if alltrue 
      then log ("unsatisfiable: " ^ its csize ^ "," ^ its dsize)
    else eval_loop44_aux expdir newd csize (dsize+1,maxdsize)
  end   

fun eval_loop44 expdir csize (dsize,maxdsize) =
  let 
    val _ = init_eval expdir
    val cmp = cpl_compare IntInf.compare IntInf.compare 
    val (_,t) =  add_time 
      (eval_loop44_aux expdir (eempty cmp) csize) (dsize,maxdsize)
  in
    log ("total time: " ^ rts_round 2 t ^ "\n")
  end
 
(* -------------------------------------------------------------------------
   Search loop
   ------------------------------------------------------------------------- *)
            
       
(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;

fun blue_edges m = 
  let 
    val i = ref 0
    fun f x = if x = 1 then incr i else ()
  in
    mat_app f m; !i
  end;
  
val graphl1 = read35 10;
val graphl2 = map (unzip_full 10) graphl1;

fun loop childl l = 
  if null l then () else
  let
    val childd = count_dict (dempty mat_compare) 
      (List.concat (map snd l));
    val l1 = map (fn (m,n) => (m, n)) (dlist childd)  
    val (child,_) = hd (dict_sort compare_imax l1);
    fun is_child x = mat_compare (child,x) = EQUAL
    fun test (a,b) = exists is_child b
    val _ = childl := child :: !childl
    val l' = filter (not o test) l
  in
    loop childl l'
  end;
fun all_subgraphs mat = 
  let
    val size = mat_size mat
    fun f x =
      let
        val l = filter (fn y => y <> x) (List.tabulate (size,I))
        val permf = mk_permf l
      in
        normalize_nauty (mat_permute (mat,size - 1) permf)
      end
  in
    mk_fast_set mat_compare (List.tabulate (size,f))
  end;

fun next_graphl graphl =
  let 
    val l = map_assoc all_subgraphs graphl
    val childl = ref [] 
  in 
    loop childl l; !childl
  end;

val graphll = 
  List.tabulate (9, fn i => (10 - i,funpow i next_graphl graphl2));

map_snd length graphll;

fun f (i,graphl) = 
  "size " ^ its i ^ "\n" ^ 
  String.concatWith "\n" (map (string_of_bluegraph_undirected) graphl) ^ "\n"
;

writel "r35_subgraphs_greedy" (map f graphll);


 (assoc 6 graphll);

average_int (map blue_edges (!childl));
*)


(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;

val expdir = selfdir ^ "/exp/r45skip";
clean_dir expdir;
eval_loop35 expdir (7,10) 14;



eval_loop35 expdir (2,7) 17;
eval_loop35 expdir (2,8) 16;
eval_loop35 expdir (2,9) 15;
eval_loop44 expdir 12 (2,12);
eval_loop44 expdir 13 (2,11);

*)     
    
(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;

val csize = 7;
val dsize = 14;
val cl = read35 csize;
val dl = read44 dsize;
val c = random_elem cl;
val d = random_elem dl;

val cl = unzip_full_edgecl csize c;
val dl = unzip_full_edgecl dsize d;
val dl' = map_fst (fn (a,b) => (a + csize, b + csize)) dl
val edgecl = cl @ dl'
val size = csize + dsize
val edgecd = edgecl_to_mat_size (csize + dsize) edgecl;
val pb0 = all_clauses3 (csize + dsize) (4,5) edgecd;

val edge_compare = cpl_compare Int.compare Int.compare;
val alllit = enew edge_compare
  (List.concat (map (map fst) pb0));
val _ = print_endline (its (elength alllit));  
  
  
val pb1 = new_clausel pb0;
val pb2 = transform_pb pb1;
val o1 = search_order_linear_undirected size;
val o2 = filter (fn (a,b) => a < csize andalso b >= csize) o1; 
val _ = print_endline (its (length o2));  
val _ = edgel_glob := elist alllit;

val (eido,colorl) = next_assign (!choose_global) (fst pb2);
val path = [([],eido,colorl)];

graph_glob := (Array2.array (size,size,0));
degree_flag := false;
iso_flag := false;
sat_solver_loop (fst pb2) (snd pb2) path;

val allvar = mk_fast_set edge_compare (List.concat (map (map fst) pb0));
val vard = dnew edge_compare (number_snd 0 allvar);
val newpb = map (map_fst (fn x => dfind x vard)) pb0;
write_satpb "aaatest" (dlength vard,newpb);
*)    


(* -------------------------------------------------------------------------
   R(4,5) brute force
   ------------------------------------------------------------------------- *)

fun random_index arr = 
  let 
    val arrn = BoolArray.length arr
    val n = random_int (0, BoolArray.length arr - 1) 
    fun loop startx x =
      if not (BoolArray.sub (arr,x)) then SOME x else 
      let val newx = (x + 1) mod arrn in
        if newx = startx then NONE else loop startx newx
      end
  in
    loop n n
  end
  handle Subscript => raise ERR "random_index" ""
  
fun random_indexl n arr = 
  if n <= 0 then [] else case random_index arr of NONE => [] | SOME i =>
  (BoolArray.update (arr,i,true); i :: random_indexl (n-1) arr)
  
  
fun subgraph_pair i subgraphs = case subgraphs of
    [] => raise ERR "subgraph_pair" ""
  | (x,(an,bn)) :: m => 
    if i < an * bn then (x, (i div bn, i mod bn)) else
    subgraph_pair (i - an * bn) m


fun send_pb dir subgraphs i =
  let
    fun pb_import () =
      let
        val (((csize,dsize),(cv,dv)),(ci,di)) = subgraph_pair i subgraphs
        val ce = Vector.sub (cv,ci)
        val de = Vector.sub (dv,di)
        val cl = unzip_full_edgecl csize (valOf (IntInf.fromString ce))
        val dl = unzip_full_edgecl dsize (valOf (IntInf.fromString de))
        val dl' = map_fst (fn (a,b) => (a + csize, b + csize)) dl
      in
        cl @ dl'
      end
    val (edgecl,t0) = add_time pb_import ()
    val _ = print_endline ("pb_import: " ^ rts_round 6 t0)
    fun pb_creation () =
      let
        val edgecd = edgecl_to_mat_size 24 edgecl 
        val pb = all_clauses3 24 (4,5) edgecd
        val allvar = mk_fast_set edge_compare (List.concat (map (map fst) pb))
        val vard = dnew edge_compare (number_snd 0 allvar)
      in
        (map (map_fst (fn x => dfind x vard)) pb, dlength vard)
      end
    val ((pb,varn),t1) = add_time pb_creation ()
    val _ = print_endline ("pb_creation: " ^ rts_round 6 t1)
    val file = dir ^ "/" ^ its i
    val fileout = file ^ "_out"
    val (_,t3) = add_time (write_satpb file) (varn,pb)
    val _ = print_endline ("write_satpb: " ^ rts_round 6 t3)
    val (_,t2) = add_time (cmd_in_dir dir) ("sh cadical.sh " ^ file)
    val _ = print_endline ("cadical: " ^ rts_round 6 t2)
    val r = mem "UNSATISFIABLE" 
     (String.tokens Char.isSpace (hd (readl fileout)))
  in 
    remove_file file; remove_file fileout; r
  end 

(* -------------------------------------------------------------------------
   R(4,5) parallel execution
   ------------------------------------------------------------------------- *)

fun init_subgraphs () = subgraphs_glob := import_subgraphs ()

fun ramseyspec_fun job = send_pb (!satdir_glob) (!subgraphs_glob) job
 

val ramseyspec : (unit, int, bool) extspec =
  {
  self_dir = selfdir,
  self = "ramsey.ramseyspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir),
     "ramsey.satdir_glob := " ^  mlquote (!satdir_glob),
     "ramsey.init_subgraphs ()"
      ] 
    ^ ")"),
  function = let fun f () pl = ramseyspec_fun pl in f end,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_int,
  read_arg = read_int,
  write_result = write_bool,
  read_result = read_bool
  }

exception Satisfiable of int list;

val batch_size = 10000

fun r45 ncore expdir =
  let
    val satdir = expdir ^ "/sat"
    val _ = satdir_glob := satdir
    val buildheapdir = expdir ^ "/buildheap"
    val completed_file = expdir ^ "/completed"
    val completedn_file = expdir ^ "/completedn"
    val _ = app mkDir_err [expdir,satdir,buildheapdir]
    val _ = cmd_in_dir selfdir ("cp cadical.sh " ^ satdir)
    val total = sum_int (map ((op *) o snd) (import_subgraphs ()))
    val arr = BoolArray.array (total,false)
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle 
       NotFound => 10000) 
    val _ = smlExecScripts.buildheap_dir := buildheapdir
    fun loop k = 
      if not (isSome (random_index arr)) then 
        (append_endline (expdir ^ "/batch") "end proof";
         print_endline "end proof")
      else
      let 
        val il = random_indexl batch_size arr
        val ncore' = Int.min (ncore,length il)
        val (bl,t) = add_time (parmap_queue_extern ncore' ramseyspec ()) il
      in
        append_endline (expdir ^ "/batch") 
          ("batch " ^ its k ^ " in " ^ rts_round 2 t ^ " seconds");
        if exists not bl then raise Satisfiable il else loop (k+1)
      end
  in
    loop 0
  end
 

  
end (* struct *)

(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;
*)

(*
(* Ramsey 3-5: 2 3 7 13 32 71 179 290 313 105 12 1 0 *)

degree_flag := true;
continue_flag := true;
disable_log := true;

fun loop (a,b) k = 
  let 
    val dir = "ramsey_" ^ its a ^ "_" ^ its b
    val file = dir ^ "/" ^ its k
    val _ = mkDir_err dir
    val (r,t) = add_time (sat_solver k) (matK a,matK b) 
  in
    print_endline (its (length (!graphl)));
    writel file (map IntInf.toString (!graphl));
    if r then () else loop (a,b) (k+1)
  end;

max_blue_degree := 4;
max_red_degree := 8; 
loop (3,5) 2;


(* Ramsey 4-4: 2 4 9 24 84 362 2079 14701 103706 
   546356 1449166 1184231 130816 640 2 1 0


*)

max_blue_degree := 8;
max_red_degree := 8; 
loop (4,4) 2;
*)

(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;

debug_flag := true;
val (r,t) = add_time (sat_solver 5) (matK 3,matK 3);
debug_flag := true;
val (r,t) = add_time (sat_solver 8) (matK 3,matK 4);
iso_flag := false;
val (r,t) = add_time (sat_solver 8) (matK 3,matK 4);
debug_flag := false;
iso_flag := false;
confinue_flag := true;

iso_flag := true;
degree_flag := true;
max_blue_degree := 5;
max_red_degree := 13; 
continue_flag := true;
val (r,t) = add_time (sat_solver 17) (matK 3,matK 6);
val (r,t) = add_time (sat_solver 14) (matK 4,matK 4);
val (r,t) = add_time (sat_solver 22) (matK 4,matK 5);
*)

(*
PolyML.print_depth 0;
load "ramsey"; load "game"; open aiLib kernel ramsey;
PolyML.print_depth 40;

val l = search_order_undirected 9;
val l = List.tabulate (9, (fn x => (x,9)));



*)

