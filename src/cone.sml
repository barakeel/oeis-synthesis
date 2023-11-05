(* =========================================================================
   Compute a set of generalized cones covering a set of cones
   ========================================================================= *)
   
structure cone :> cone =
struct   

open HolKernel Abbrev boolLib aiLib kernel 
  rconfig graph nauty sat ramseySyntax gen
val ERR = mk_HOL_ERR "cone"
type vleafs = int * int * (IntInf.int * int list) list  

(* -------------------------------------------------------------------------
   Cone generalization
   ------------------------------------------------------------------------- *)

val cone_compare = list_compare Int.compare
val cone_set = mk_fast_set cone_compare   

fun parents cl = case cl of 
    [] => []
  | a :: m => 
    if a <> 0 
    then (0 :: m) :: map (fn x => a :: x) (parents m)
    else map (fn x => a :: x) (parents m)
  
fun instances cl = 
  let val cl' =  map (fn x => if x = 0 then [1,2] else [x]) cl in 
    cartesian_productl cl'
  end
  
fun cnext uset childl = 
  let  
    val childset = enew (list_compare Int.compare) childl
    val l1 = cone_set (List.concat (map parents childl))
    fun is_fullanc m = all (fn x => emem x uset) (instances m)
    val l2 = filter is_fullanc l1
  in
    l2
  end

fun cloop uset childl =
  let val parentl = cnext uset childl in
    if null parentl
    then random_elem childl
    else cloop uset parentl
  end;
  
fun cgeneralize uset leaf = cloop uset [leaf];
  
fun n_hole cl = length (filter (fn x => x = 0) cl);  
  
val attempts_glob = ref 100
  
fun ccover_loop uset = 
  if elength uset <= 0 then [] else 
  let 
    val (parentl1,t) = add_time 
      (map (cgeneralize uset)) (random_subset (!attempts_glob) (elist uset))
    fun uncovered_instances parent = 
      (parent, filter (fn x => emem x uset) (instances parent))
    val parentl2 = map uncovered_instances parentl1
    val parentl3 = map_assoc (length o snd) parentl2
    val ((parent,leafs),sc) = hd (dict_sort compare_imax parentl3)
    val newuset = ereml leafs uset
    (* val _ = log (its (elength newuset) ^ " " ^ rts_round 2 t) *)
  in
    (parent,leafs) :: ccover_loop newuset
  end

fun string_of_cone cone = String.concatWith "_" (map its cone)
fun cone_of_string s = map string_to_int (String.tokens (fn x => x = #"_") s)

fun write_cone (bluen,redn) mati conel =
  let
    val dir = selfdir ^ "/ramsey_cone"
    val size = mat_size (unzip_mat mati)
    val file = dir ^ "/" ^ its bluen ^ its redn ^ its size ^ "_" ^ infts mati
    val _ = mkDir_err dir
    fun f (cone,conel) = 
      String.concatWith " " (map string_of_cone (cone :: conel)) 
  in
    writel file (map f conel)
  end
  
fun read_cone (bluen,redn) mati = 
  let
    val dir = selfdir ^ "/ramsey_cone"
    val size = mat_size (unzip_mat mati)
    val file = dir ^ "/" ^ its bluen ^ its redn ^ its size ^ "_" ^ infts mati
    fun f s = 
      let val l = map cone_of_string (String.tokens Char.isSpace s) in
        (hd l, tl l)
      end
  in
    map f (readl file)
  end
  
fun gen_cone (bluen,redn) mati = 
  let
    val mat = unzip_mat mati
    val size = mat_size mat
    val _ = (disable_log := true;
             iso_flag := false; proof_flag := false; debug_flag := false)
    val matl = sat_solver_edgecl (mat_to_edgecl mat) (size+1) (bluen,redn)
    val _ = disable_log := false
    val _ = log ("models: " ^ its (length matl))
    fun pairbelowy y = List.tabulate (y,fn x => (x,y))
    val edgel = pairbelowy size
    fun mat_to_cone mx = map (fn (x,y) => mat_sub (mx,x,y)) edgel
    val conel1 = map mat_to_cone matl
    val coneset = enew cone_compare conel1 
    val _ = log ("cones: " ^ its (elength coneset))
    val conel3 = ccover_loop coneset
    val _ = log ("cone generalizations: " ^ its (length conel3))
  in
    write_cone (bluen,redn) mati conel3
  end


fun write_infset file (a,b) = writel file [its a,its b]
fun read_infset file = case readl file of
    [sa,sb] => (string_to_int sa, string_to_int sb)
  | _ => raise ERR "read_infset" ""
 
fun write_inf file i = writel file [infts i]
fun read_inf file = stinf (singleton_of_list (readl file))


val conespec : (int * int, IntInf.int, unit) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "cone.conespec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = gen_cone,
  write_param = write_infset,
  read_param = read_infset,
  write_arg = write_inf,
  read_arg = read_inf,
  write_result = let fun f file _ = () in f end,
  read_result = let fun f file = () in f end
  }

fun cones45 ncore size (bluen,redn) =
  let 
    val s = its bluen ^ its redn ^ its size
    val expdir = selfdir ^ "/exp"
    val dir = expdir ^ "/cone" ^ s
    val _ = app mkDir_err [expdir,dir]
    val _ = smlExecScripts.buildheap_dir := dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle 
       NotFound => 10000) 
    val par = read_par size (bluen,redn)
    val parn = length par
    val _ = log ("par : " ^ its parn)
    val n' = Int.min (parn,ncore)
    val (_,t) = add_time (smlParallel.parmap_queue_extern n' conespec (4,5)) par
  in
    log ("cones: " ^ rts_round 4 t)
  end


(*
PolyML.print_depth 0;
load "gen"; load "sat"; load "cone";
open aiLib kernel graph sat nauty gen rconfig cone;
PolyML.print_depth 10;

val ncore = 60;
range (14,17, fn i => cones45 ncore i (4,4));
range (12,13, fn i => cones45 ncore i (3,5));

*)


(* cone proof 
PolyML.print_depth 0;
load "gen"; load "sat"; load "cone";
open aiLib kernel graph sat nauty gen rconfig cone ramseySyntax;
PolyML.print_depth 10;

val mati = hd (read_par 14 (4,4));
val mat = unzip_mat mati;
val size = mat_size mat;
val cone = read_cone (4,5) mati; 
val conegen = map fst cone;

val _ = conep_flag := true;


fun create_parconethmd (bluen,redn) mi = 
  let 
    val parl = map fst (read_cone (bluen,redn) mi) 
    val size = mat_size (unzip_mat mi)
    val col = List.tabulate (size,fn i => (i,size))
  in
    if null parl then dempty cone_compare else
    let
      fun f parcone =
        let
          val colc = combine (col,parcone)
          val term = term_of_edgecl (size + 1) colc
        in
          ASSUME term
        end
    in
      dnew cone_compare (map_assoc f parl)
    end
  end

val parconethmd = create_parconethmd (4,5) mati;



val _ = (disable_log := true;conep_flag := true;
         iso_flag := false; proof_flag := true; debug_flag := false);
val matl = sat_solver_edgecl (mat_to_edgecl mat) (size+1) (bluen,redn)


*)


end (* struct *)






