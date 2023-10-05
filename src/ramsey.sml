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

fun write35gen csize matl = 
  writel (selfdir ^ "/ramsey_3_5_gen/" ^ its csize) (map szip_mat matl)
fun write44gen dsize matl = 
  writel (selfdir ^ "/ramsey_4_4_gen/" ^ its dsize) (map szip_mat matl)



(* -------------------------------------------------------------------------
   Glueing pairs using Cadical
   ------------------------------------------------------------------------- *)

fun glue_filein dir (ci,di) =
  let
    val file = dir ^ "/sat"
    val (ce,de) = (unzip_mat ci, unzip_mat di)
    val pbid = szip_mat ce ^ "-" ^ szip_mat de
    val _ = write_assignl file (read_mapping file) pbid (ce,de);
    val fileclauses = file ^ "_clauses"
    val fileassign = file ^ "_assign_" ^ pbid
    val filein = file ^ "_in_" ^ pbid
  in
    cmd_in_dir dir 
      ("cat " ^ fileassign ^ " " ^ fileclauses ^ " > " ^ filein);
    remove_file fileassign;
    filein
  end

fun glue dir (ci,di)  = 
  let
    val filein = glue_filein dir (ci,di)
    val fileout = filein ^ "_result"
    val (_,t2) = add_time (cmd_in_dir dir) ("sh cadical.sh " ^ filein)
    val sl = readl fileout
    val r = mem "UNSATISFIABLE" (String.tokens Char.isSpace (hd sl))
    val sats = if r then "unsat" else ("sat " ^ hd (tl sl))
  in
    app remove_file [filein,fileout];
    print_endline (String.concatWith " "
      [IntInf.toString ci, IntInf.toString di, sats, rts_round 4 t2]);
    r
  end

(* -------------------------------------------------------------------------
   R(4,5) parallel execution
   ------------------------------------------------------------------------- *)

fun ramseyspec_fun () (m1,m2) = 
  let val satdir = OS.Path.dir (!smlExecScripts.buildheap_dir) ^ "/sat" in
    glue satdir (m1,m2)
  end
  
fun write_matpair file (m1,m2) = writel file (map infts [m1,m2])
fun read_matpair file = pair_of_list (map stinf (readl file)) 
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

fun r45 ncore expname csize =
  let
    val dsize = 24 - csize
    val expdir = selfdir ^ "/exp/" ^ expname
    val buildheapdir = expdir ^ "/buildheap"
    val satdir = expdir ^ "/sat"
    val _ = app mkDir_err [selfdir ^ "/exp",expdir,satdir,buildheapdir]
    val _ = write_r45_pb (satdir ^ "/sat");
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
 

 
fun read_stats expname =
  let
    val dir = selfdir ^ "/exp/" ^ expname ^ "/buildheap";
    val filel = map (fn x => dir ^ "/" ^ x) (listDir dir);
    val sl = List.concat (map readl filel)
    fun f s = 
      let val (a,b,c,d) = quadruple_of_list (String.tokens Char.isSpace s) in
        if c <> "unsat" then raise ERR "sat" "" else
        ((sunzip_mat a, sunzip_mat b), streal d)
      end
    val rl = map f sl;  
    val rlsorted =  dict_sort compare_rmin rl
  in
    rlsorted
  end
  
fun convert olddir newdir =
  let
    fun convert_file file = 
      let 
        val size = string_to_int file 
        val sl = readl (olddir ^ "/" ^ file)
        val ml = map (unzip_full size o stinf) sl
      in
        writel (newdir ^ "/" ^ file) (map szip_mat ml)
      end
  in
    mkDir_err newdir;
    app convert_file (listDir olddir)
  end
  
end (* struct *)


(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey graph;
PolyML.print_depth 10;
convert "ramsey_3_5_oldformat" "ramsey_3_5";
convert "ramsey_4_4_oldformat" "ramsey_4_4";
*)

(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey satenc graph;
PolyML.print_depth 10;
mkDir_err "test";
val satdir = selfdir ^ "/test";
write_r45_pb "test/sat";
val (cl,dl) = (read35 7,read44 17); 
val (ce,de) = (random_elem cl, random_elem dl);
cmd_in_dir selfdir ("cp cadical.sh " ^ satdir);
glue satdir (ce,de);
*)


(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey graph;
PolyML.print_depth 10;

val csize = 10;
val l = read35 csize; 
val gen0 =  map unzip_mat l;
val (mp,cover) = split (compute_cover gen0);
val mpdesc = enew mat_compare (List.concat (map all_leafs mp));
all (fn x => emem x mpdesc) gen0;
mkDir_err "ramsey_3_5_gen";
writel ("ramsey_3_5_gen/" ^ its csize) (map szip_mat mp);
writel "r45_cover35_10_stats" (map (its o length) cover);
*)

(* r45 100 "r45_10" 10; *)
(* no_gen 7 *)
(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;
r45 100 "r45_7" 7;
*)

(* stats
PolyML.print_depth 0;
load "aiLib"; open aiLib;
PolyML.print_depth 10;

val dir = selfdir ^ "/exp/r45_7/buildheap";
val ERR = mk_HOL_ERR "test";
val ((ci,di),_) = hd rlsorted;
val c = unzip_mat ci;
val d = unzip_mat di;

*)

(* stats
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey graph;
PolyML.print_depth 10;
val childrenl = map unzip_mat (read35 7);
val (a,b) = split (compute_cover childrenl);
length a; map length b;


val c = normalize_nauty (hd a);
val d = normalize_nauty (unzip_mat (hd (read44 17)));


fun 


*)



