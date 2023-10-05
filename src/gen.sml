(* =========================================================================
   Compute a set of genralized graphs covering a set of graphs
   ========================================================================= *)
   
structure gen :> gen =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty 
  rconfig satenc smlParallel
val ERR = mk_HOL_ERR "gen"

(* -------------------------------------------------------------------------
   Going up and down in the tree
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
      in 
        l := newm :: !l
      end
  in
    mat_appi f mat; nauty_set (!l)
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
        app h edgecl; newm
      end
    val childl = map g edgecll
  in
    nauty_set childl
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
      let val newm = mat_copy mat in
        mat_update_sym (newm,i,j,c); newm
      end
    val childl = map g edgecl
  in
    nauty_set childl
  end;  
  
fun all_descendants_aux n ml =
  if n <= 0 then ml else
  let val l = List.concat (map all_children ml) in
    all_descendants_aux (n-1) (mk_fast_set mat_compare l)
  end
fun all_descendants n m = all_descendants_aux n [m] 

(* -------------------------------------------------------------------------
   Generalization of a set of graphs with the same size and the 
   same number of holes in their coloring
   ------------------------------------------------------------------------- *)

val gen_width = ref 10  
     
fun next_hgen minhole leafd l = 
  let  
    val l1 = mk_fast_set mat_compare (List.concat (map all_parents l))
    val ndiff = number_of_holes (hd l1) - minhole
      handle Empty => raise ERR "next_hgen" ""
    fun is_fullanc m = all (fn x => emem x leafd) (all_descendants ndiff m)
    val l2 = filter is_fullanc l1;
  in
    random_subset (!gen_width) l2
  end;

fun loop_hgen ngen minhole leafd l =
  let
    val (nextl,t) = add_time (next_hgen minhole leafd) l
    val _ = print_endline (its (ngen+1) ^ ": " ^ 
      its (length nextl) ^ " in " ^ rts_round 4 t ^ " seconds")
  in
    if null nextl then l else loop_hgen (ngen + 1) minhole leafd nextl
  end;
  
fun hgeneralize minhole leafd leaf = 
  loop_hgen 0 minhole leafd [leaf]

fun cover_score minhole coverd mp =
  let val ndiff = number_of_holes mp - minhole in
    length (filter (fn x => not (emem x coverd)) (all_descendants ndiff mp))
  end
  
fun find_best_mpl minhole coverd mpl =
  let 
    val f = cover_score minhole coverd
    val l = dict_sort compare_imax (map_assoc f mpl) 
  in
    hd l
  end
  
fun loop_hcover minhole leafs leafd coverd uncover result =
  if null uncover then rev result else
  let 
    val m0 = random_elem uncover
    val (mpl,t1) = add_time (hgeneralize minhole leafd) m0
    val ((mp,sc),t2) = add_time (find_best_mpl minhole coverd) mpl
    val ndiff = number_of_holes mp - minhole
    val mcover = filter (fn x => not (emem x coverd)) (all_descendants ndiff mp) 
    val mcoverd = enew mat_compare mcover
    val newcoverd = eaddl mcover coverd
    val newuncover = filter (fn x => not (emem x mcoverd)) uncover
    val _ = print_endline (
      "Covering " ^ its sc ^ " graphs (" ^ 
      its (length newuncover) ^ " remaining)" ^
      " in " ^ rts_round 4 t1 ^ " seconds and in " ^ 
      rts_round 4 t2 ^ " seconds")
  in  
    loop_hcover minhole leafs leafd newcoverd newuncover ((mp,mcover) :: result)
  end;
  
fun compute_hcover leafs = 
  let 
    val leafd = enew mat_compare leafs 
    val minhole = number_of_holes (hd leafs)  
  in 
    loop_hcover minhole leafs leafd (eempty mat_compare) leafs [] 
  end  
   
(* -------------------------------------------------------------------------
   Generalization (from a set of leafs)
   ------------------------------------------------------------------------- *) 

fun next_gen leafd l = 
  let  
    val l1 = mk_fast_set mat_compare (List.concat (map all_parents l))
    fun is_fullanc m = all (fn x => emem x leafd) (all_leafs m)
    val l2 = filter is_fullanc l1;
  in
    random_subset (!gen_width) l2
  end;

fun loop_gen ngen leafd l result =
  let
    val (nextl,t) = add_time (next_gen leafd) l
    val _ = print_endline (its (ngen+1) ^ ": " ^ 
      its (length nextl) ^ " in " ^ rts_round 4 t ^ " seconds")
  in
    if null nextl then rev result else 
    loop_gen (ngen + 1) leafd nextl (l :: result)
  end;
  
fun generalize leafd leaf = loop_gen 0 leafd [leaf] []

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

end (* struct *)

(* 
load "gen"; open kernel aiLib gen;



*)
