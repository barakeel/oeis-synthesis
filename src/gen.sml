(* =========================================================================
   Compute a set of genralized graphs covering a set of graphs
   ========================================================================= *)
   
structure gen :> gen =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty sat rconfig
  rconfig satenc smlParallel
val ERR = mk_HOL_ERR "gen"

val nauty_time = ref 0.0
val normalize_nauty = total_time nauty_time normalize_nauty

(* -------------------------------------------------------------------------
   Going up and down in the tree
   ------------------------------------------------------------------------- *) 

fun apply_coloring m edgecl = 
   let 
     val newm = mat_copy m
     fun f ((i,j),c) = mat_update_sym (newm,i,j,c) 
   in
     app f edgecl; newm
   end

fun all_coloring edgel = 
  let
    val edgebothl =
      let 
        val l = ref []
        fun f (i,j) = l := [((i,j),blue),((i,j),red)] :: !l 
      in 
        (app f edgel; !l)
      end
  in
    cartesian_productl edgebothl
  end
        
        
fun all_parents m = 
  let
    val l = ref []
    fun f (i,j,x) =
      if x = 0 then () else 
      let 
        val newm = mat_copy m
        val _ = mat_update_sym (newm,i,j,0)
      in 
        l := newm :: !l
      end
  in
    mat_traverse f m; nauty_set (!l)
  end
  
fun all_children m = 
  let
    val l = ref []
    fun f (i,j,x) =
      if x <> 0 then () else 
      let 
        val bluem = mat_copy m
        val _ = mat_update_sym (bluem,i,j,blue)
        val redm = mat_copy m
        val _ = mat_update_sym (redm,i,j,red)
      in 
        l := bluem :: redm :: !l
      end
  in
    mat_traverse f m; nauty_set (!l)
  end 
  
fun all_existing_children set m = 
  let
    val rset = ref (eempty mat_compare)
    fun f (i,j,x) =
      if x <> 0 then () else 
      let 
        val bluem = mat_copy m
        val _ = mat_update_sym (bluem,i,j,blue)
        val normbluem = normalize_nauty bluem
        val redm = mat_copy m
        val _ = mat_update_sym (redm,i,j,red)
        val normredm = normalize_nauty redm
        fun add m = if emem m set then rset := eadd m (!rset) else ()
      in 
        add normbluem; add normredm
      end
  in
    mat_traverse f m; elist (!rset)
  end  

fun all_leafs m =
  let
    val edgel = all_holes m
    val coloringl = all_coloring edgel
    val childl = map (apply_coloring m) coloringl
  in
    nauty_set childl
  end;


(* -------------------------------------------------------------------------
   Global generalization
   ------------------------------------------------------------------------- *) 

fun all_parents_fair siblingd resultd m = 
  let
    fun f (i,j,x) =
      if x = 0 then () else 
      let 
        val sibm = mat_copy m
        val _ = mat_update_sym (sibm,i,j,3-x)
        val normsibm = zip_mat (normalize_nauty sibm)
      in 
        if emem normsibm siblingd then
          let 
            val parentm = mat_copy m
            val _ = mat_update_sym (parentm,i,j,0)
            val normparentm = zip_mat (normalize_nauty parentm)
          in 
            resultd := eadd normparentm (!resultd)
          end
        else ()
      end
  in
    mat_traverse f m
  end

fun ggeneralize_one childl = 
  let
    fun test m = number_of_blueedges m mod 2 = 0
    val (evenl,oddl) = partition test childl
    val (selectl,siblingd) = 
      if length evenl <= length oddl 
      then (evenl, enew IntInf.compare (map zip_mat oddl))  
      else (oddl, enew IntInf.compare (map zip_mat evenl))
    val resultd = ref (eempty IntInf.compare)
    val parentl = app (all_parents_fair siblingd resultd) selectl
  in
    map unzip_mat (elist (!resultd))
  end;

fun compute_pardescd level leafd childescd childset parentl =
  let
    fun lookup_desc x = dfind x childescd handle NotFound => []
    fun all_desc m = List.concat (map lookup_desc 
      (all_existing_children childset m))
    fun all_desc_extra m = m :: all_desc m
    val extral = dfind (level+1) leafd handle NotFound => [] 
    val extraset = enew mat_compare extral
    val _ = log ("  " ^ its (elength extraset) ^ " extra")
    val parentnotextral = filter (fn x => not (emem x extraset)) parentl
    val parentandextral = 
      map_assoc (mat_set o all_desc) parentnotextral @
      map_assoc (mat_set o all_desc_extra) extral           
  in
    dnew mat_compare parentandextral
  end
  
fun loop_ggen level leafd childescd result = 
  let
    val childl = dkeys childescd
    val childset = enew mat_compare childl
    val (parentl,t) = add_time ggeneralize_one childl
    val _ = log (its (level+1) ^ ": " ^ 
      its (length parentl) ^ " parents in "  ^ 
      rts_round 4 t ^ " seconds")
    val (pardescd,t) = add_time 
      (compute_pardescd level leafd childescd childset) parentl
    val _ = log ("  " ^ its (dlength pardescd) ^ 
      " parents with descendants in " ^ rts_round 4 t ^ " seconds")  
    val childset_small = enew mat_compare 
      (List.concat (map (all_existing_children childset) (dkeys pardescd)))   
    val _ = log ("  " ^ its (elength childset_small) ^ " children")
    val orphanl = filter (fn (x,_) => not (emem x childset_small)) 
      (dlist childescd)
    val newresult = orphanl @ result
    val _ = log ("  " ^ its (length orphanl) ^ " orphans")
    val newleafd = drem level leafd
  in
    if dlength pardescd <= 0 andalso dlength newleafd <= 0 
    then newresult 
    else loop_ggen (level + 1) newleafd pardescd newresult
  end

fun ggeneralize leafl = 
  let 
    val leafd = dregroup Int.compare 
      (map swap (map_assoc number_of_holes leafl))
    val minlevel = list_imin (dkeys leafd) 
    val extral = dfind minlevel leafd
    val childescd = dnew mat_compare (map (fn x => (x,[x])) extral)
    val orphanl = loop_ggen minlevel leafd childescd []
    val leafset1 = dict_sort mat_compare leafl
    val leafset2 = mk_fast_set mat_compare (List.concat (map snd orphanl))
  in
    if list_compare mat_compare (leafset1,leafset2) <> EQUAL
    then raise ERR "ggeneralize" 
      (its (length leafset1) ^ " <> " ^ its (length leafset2))
    else orphanl
  end
  
(* -------------------------------------------------------------------------
   Minimizing a cover
   ------------------------------------------------------------------------- *)

fun dreml l d = foldl (uncurry drem) d l

fun minimize_cover_aux cover leafset result = 
  if elength leafset <= 0 then rev result else 
  if null cover then raise ERR "minimize_cover" (its (elength leafset)) else
  let 
    val coveri = map_assoc (elength o snd) cover
    val ((best,bestd),sc) = hd (dict_sort compare_imax coveri)
    val newleafset = ereml (elist bestd) leafset
    val _ = log ("covering " ^ its sc ^ " remaining " ^ 
                           its (elength newleafset))
    fun f (x,d) =
      let val newd = ereml (elist bestd) d in
        if elength newd <= 0 then NONE else SOME (x,newd)
      end
    val newcover = List.mapPartial f cover
  in
    minimize_cover_aux newcover newleafset (best :: result)
  end

fun minimize_cover leafl cover =
  let
    val leafset = enew mat_compare leafl
    val cover' = map_snd (enew mat_compare) cover
    val (result,t) = add_time (minimize_cover_aux cover' leafset) []
    val _ = log ("mini: " ^ rts_round 4 t)
  in
    result
  end

(* -------------------------------------------------------------------------
   Search algorithm
   ------------------------------------------------------------------------- *)

fun all_models n cover =
  let fun f m = sat_solver_edgecl (mat_to_edgecl m) n (4,5) in
    nauty_set (List.concat (map f cover))
  end;
  
val cover_glob = ref []
fun next_cover stopn (cover,n) =
  let 
    val _ = log ("## START SIZE " ^ its (n+1) ^ " ##")
    val (model',t) = add_time (all_models (n+1)) cover
    val model = nauty_set model'
    val _ = log ("### MODEL: " ^ its (length model) ^
      " in " ^ rts_round 4 t ^ " seconds")
    val (covera,t) = add_time ggeneralize model
    val _ = log ("### COVERA: " ^ its (length covera) ^
      " in " ^ rts_round 4 t ^ " seconds")
    val leafset = enew mat_compare model
    val (coverb,t) = add_time (minimize_cover model) covera
    val _ = log ("### COVERB: " ^ its (length coverb) ^
      " in " ^ rts_round 4 t ^ " seconds")
    val _ = log ("## END SIZE " ^ its (n+1) ^ " ##")
  in
    cover_glob := (coverb,n+1) :: !cover_glob;
    if n+1 >= stopn then !cover_glob else next_cover stopn (coverb,n+1)  
  end

(* -------------------------------------------------------------------------
   Generalization (from a set of leafs)
   ------------------------------------------------------------------------- *) 

val gen_width = ref 10  
val gen_depth = ref 100

fun next_gen leafd l = 
  let  
    val l1 = mat_set (List.concat (map all_parents l))
    fun is_fullanc m = all (fn x => emem x leafd) (all_leafs m)
    val l2 = filter is_fullanc l1;
  in
    random_subset (!gen_width) l2
  end;

fun loop_gen ngen leafd l result =
  let
    val (nextl,t) = add_time (next_gen leafd) l
    val _ = log (its (ngen+1) ^ ": " ^ 
      its (length nextl) ^ " in " ^ rts_round 4 t ^ " seconds")
  in
    if null nextl then rev result else 
    loop_gen (ngen + 1) leafd nextl (l :: result)
  end;
  
fun generalize leafd leaf = loop_gen 0 leafd [leaf] []

fun cover_score coverd mp =
  length (filter (fn x => not (emem x coverd)) (all_leafs mp))

fun find_best_mpl coverd mpl =
  hd (dict_sort compare_imax (map_assoc (cover_score coverd) mpl))

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
    val _ = log (
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
