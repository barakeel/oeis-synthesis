(* convention: 
1) false means continue and true means stop 
2) shapes are small graphs with blue edges (blue = 1)
*)
   
structure ramsey :> ramsey =
struct   

open HolKernel Abbrev boolLib aiLib kernel smlParallel
val ERR = mk_HOL_ERR "ramsey"

(* -------------------------------------------------------------------------
   Config file
   ------------------------------------------------------------------------- *)

val ramseyconfigd = 
  if exists_file (selfdir ^ "/ramsey_config") then 
    let 
      val sl = readl (selfdir ^ "/ramsey_config")
      fun f s = SOME (pair_of_list (String.tokens Char.isSpace s)) 
        handle HOL_ERR _ => NONE
    in
      dnew String.compare (List.mapPartial f sl)
    end
  else dempty String.compare

fun bflag s b = 
  string_to_bool (dfind s ramseyconfigd) handle NotFound => b
fun iflag s i = 
  string_to_int (dfind s ramseyconfigd) handle NotFound => i
fun rflag s r = 
  valOf (Real.fromString (dfind s ramseyconfigd)) handle NotFound => r

val real_time = rflag "real_time" 0.0
val abstract_time = iflag "abstract_time" 0
val memory = iflag "memory" 10000

val symmetry_flag = ref false

(* flags conspiring to output all models *)
val continue_flag = ref false
val sat_flag = ref false

(* experimental flags *)
val shuffle_flag = ref false

(* -------------------------------------------------------------------------
   Logging
   ------------------------------------------------------------------------- *)

fun log s = print_endline s 

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val blue = 1
val red = 2
val blue_supershapes_glob = ref (Array.fromList [true])
val red_supershapes_glob = ref (Array.fromList [true])
(*
val blue_prop_glob = ref (Array.fromList [[(0,0)]])
val red_prop_glob = ref (Array.fromList [[(0,0)]])
*)
val edgel_glob = ref []
val blue_size_glob = ref 0
val red_size_glob = ref 0
val counter = ref 0
val limit_glob = 
  (if abstract_time > 0 then SOME abstract_time else NONE, 
   if real_time > 0.0 then SOME (Time.fromReal real_time) else NONE)
val timer = ref (Timer.startRealTimer ())
val isod_glob = ref (eempty IntInf.compare)

(* -------------------------------------------------------------------------
   Timer and statistics
   ------------------------------------------------------------------------- *)

exception RamseyTimeout;

val level1 = ref 0
val level2 = ref 0
val level3 = ref 0
val level4 = ref 0

fun init_timer () =
  (level1 := 0;
   level2 := 0;
   level3 := 0;
   level4 := 0;
   counter := 0; 
   timer := Timer.startRealTimer ())

fun test_timer () =
  let
    val _ = incr counter
    val _ = if !counter mod 1000 = 0 then print "." else ()
    val _ = case fst (limit_glob) of NONE => () | SOME ti => 
      if !counter > ti then raise RamseyTimeout else ()
    val _ = case snd (limit_glob) of NONE => () | SOME tr => 
      if Timer.checkRealTimer (!timer) > tr then raise RamseyTimeout else ()
  in
    ()
  end

(* -------------------------------------------------------------------------
   Adjacency matrix representation
   ------------------------------------------------------------------------- *)

type mat = int Array2.array
fun mat_sub (m,i,j) = Array2.sub (m,i,j)

fun mat_tabulate (n,f) = Array2.tabulate Array2.RowMajor (n,n,f)
fun mat_appi f m = 
  let val range = {base=m,row=0,col=0,nrows=NONE,ncols=NONE} in
    Array2.appi Array2.RowMajor f range
  end

fun size_of_zip l =
  let val ln = length l in
    valOf (List.find (fn x => x * (x - 1) = ln) (List.tabulate (100,I)))
  end
  
local open IntInf in

fun zip_mat m =
  let val r = ref 1 in
    mat_appi (fn (i,j,x) => if i = j then () else 
                            r := !r * 3 + IntInf.fromInt x) m; !r
  end
fun unzip_mat mati = 
  let 
    fun loop x = if x < 3 then [] else x mod 3 :: loop (x div 3) 
    val l = ref (rev (loop mati))
    val graphsize = size_of_zip (!l)
    fun f (i,j) = if i = j then 0 else 
      let val r = IntInf.toInt (hd (!l)) in l := tl (!l); r end 
  in
    mat_tabulate (graphsize, f)
  end     
  
end (* local *)

fun szip_mat m = IntInf.toString (zip_mat m)
fun sunzip_mat s = unzip_mat (valOf (IntInf.fromString s))


(* sigma is the inverse permutation *)
fun mat_permute (m,size) sigma =
  let fun f (x,y) = mat_sub (m, sigma x, sigma y) in
    mat_tabulate (size, f)
  end
  
fun random_mat size = 
  mat_tabulate (size,fn (a,b) => if a=b then 0 else random_int (0,2));
fun mat_size m = 
  let val (a,b) = Array2.dimensions m in
    if a = b then a else raise ERR "mat_size" ""
  end 
fun random_shape size color =
   mat_tabulate (size,fn (a,b) => if a=b then 0 else 
    if random_real () < 0.5 then 0 else color)

fun symmetrify m = 
  mat_tabulate (mat_size m, fn (a,b) => 
  if a=b then 0 else if a < b then mat_sub (m,a,b) else mat_sub (m,b,a));

fun random_symmat size = symmetrify (random_mat size);
 
fun mat_compare_aux size a1 a2 i j = 
  case Int.compare (Array2.sub (a1,i,j),Array2.sub (a2,i,j)) of
      EQUAL => if j >= size - 1 then 
                 if i >= size - 1 
                 then EQUAL 
                 else mat_compare_aux size a1 a2 (i+1) 0
               else mat_compare_aux size a1 a2 i (j+1)
    | r => r;

fun mat_compare_fixedsize size (a1,a2) = 
  mat_compare_aux size a1 a2 0 0;

fun mat_compare (a1,a2) = 
  case Int.compare (mat_size a1, mat_size a2) of
    EQUAL => mat_compare_aux (mat_size a1) a1 a2 0 0
  | x => x 
 
(* warning : overwrites *)
fun mat_add (edge,color) graph  =
  let 
    val graphsize = mat_size graph 
    val newgraphsize = Int.max (Int.max edge + 1, graphsize)  
  in
    if !symmetry_flag then 
      mat_tabulate (newgraphsize, fn (i,j) => 
      if (i,j) = edge orelse (j,i) = edge then color 
      else if i >= graphsize orelse j >= graphsize then 0
      else mat_sub (graph,i,j))
    else
      mat_tabulate (newgraphsize, fn (i,j) => 
      if (i,j) = edge then color 
      else if i >= graphsize orelse j >= graphsize then 0
      else mat_sub (graph,i,j))
  end
  
fun mat_addl edgecl graph = foldl (uncurry mat_add) graph edgecl

(* assumes shape contains 1 and 0s and is not too big *)    
fun shape_to_int_fixedsize m = 
  let val r = ref 0 (* can start at zero because all the same size *) in
    mat_appi (fn (i,j,x) => if i = j then () else r := !r * 2 + x) m; !r
  end
    
fun shape_to_int m = 
  let val r = ref 1 in
    mat_appi (fn (i,j,x) => if i = j then () else r := !r * 2 + x) m; !r
  end

fun neighbor_of color graph x = 
  let 
    val vertexl = List.tabulate (mat_size graph,I)
    fun test y = mat_sub (graph,x,y) = color
  in
    filter test vertexl
  end
  
fun all_neighbor color graph = 
  List.tabulate (mat_size graph, neighbor_of color graph) 

fun inneighbor_of color graph x = 
  let 
    val vertexl = List.tabulate (mat_size graph,I)
    fun test y = mat_sub (graph,y,x) = color
  in
    filter test vertexl
  end

fun string_of_edgecl edgecl = 
  let fun f ((i,j),x) = its i ^ "-" ^ its j ^ ":" ^ its x in
    String.concatWith " " (map f edgecl)
  end

fun string_of_edgel edgecl = 
  let fun f (i,j)= its i ^ "-" ^ its j in
    String.concatWith " " (map f edgecl)
  end
  
fun named_neighbor color graph = number_fst 0 (all_neighbor color graph)  
  
fun string_of_graph graph = 
  let fun f (i,l) = its i ^ " -> " ^ String.concatWith " " (map its l) in
    String.concatWith ", " (map f (named_neighbor blue graph)) ^ " | " ^
    String.concatWith ", " (map f (named_neighbor red graph))
  end
  
fun string_of_shape graph = 
  let fun f (i,l) = its i ^ " -> " ^ String.concatWith " " (map its l) in
    String.concatWith ", " (map f (named_neighbor blue graph))
  end

(* -------------------------------------------------------------------------
   Switching between representations
   ------------------------------------------------------------------------- *)

fun mat_to_edgecl m =
  let 
    val r = ref []
    fun f (i,j,x) = if x = 0 then () else 
      r := ((i,j),x) :: !r
  in
    mat_appi f m; !r
  end
  
fun mat_to_edgecl_undirected m =
  let 
    val r = ref []
    fun f (i,j,x) = if x = 0 orelse i >= j then () else 
      r := ((i,j),x) :: !r
  in
    mat_appi f m; !r
  end  

fun edge_conflict edgecl =
  let 
    val d = ref (dempty (cpl_compare Int.compare Int.compare)) 
    fun loop l = case l of 
      [] => SOME (dlist (!d)) 
    | (edge,c) :: m => 
      (
      case dfindo edge (!d) of
        NONE => (d := dadd edge c (!d); loop m)
      | SOME c' => if c = c' then loop m else NONE 
      )
  in
    loop edgecl
  end

fun edgecl_to_mat edgecl =
  let 
    val edgel = map fst edgecl
    val edged = dnew (cpl_compare Int.compare Int.compare) edgecl
    val size = list_imax (List.concat (map (fn (a,b) => [a,b]) edgel)) + 1
    fun f (i,j) = case dfindo (i,j) edged of NONE => 0 | SOME c => c 
  in
    mat_tabulate (size, f)
  end
  
fun edgel_to_shape edgel =
  let
    val edged = enew (cpl_compare Int.compare Int.compare) edgel
    val size = list_imax (List.concat (map (fn (a,b) => [a,b]) edgel)) + 1
    fun f (i,j) = if emem (i,j) edged then 1 else 0 
  in
    mat_tabulate (size, f)
  end  

(* -------------------------------------------------------------------------
   Permutations
   ------------------------------------------------------------------------- *)
 
fun insert_everywhere elem l = case l of 
    [] => [[elem]]
  | a :: m => (elem :: a :: m) :: 
    map (fn m' => a::m') (insert_everywhere elem m);

fun permutations l = case l of 
    [] => [[]] 
  | a :: m => List.concat (map (insert_everywhere a) (permutations m));

fun mk_permf perm = 
  let 
    val permv = Vector.fromList perm
    fun f n = Vector.sub (permv,n) 
  in 
    f 
  end 

(* -------------------------------------------------------------------------
   Properties of graph
   ------------------------------------------------------------------------- *)

fun is_ackset shape =
  let val neighborl = all_neighbor 1 shape in
    length (mk_fast_set (list_compare Int.compare) neighborl) =
    length neighborl
  end;

fun is_ackset_pb (shape1,shape2) = 
  is_ackset shape1 andalso is_ackset shape2;

fun not_automorphic shape =
  let 
    val shapesize = mat_size shape
    val perml0 = permutations (List.tabulate (shapesize, I))
    fun f x = mat_permute (shape,shapesize) (mk_permf x)
    val matl = map f perml0
  in
    length (mk_fast_set (mat_compare_fixedsize shapesize) matl) =
    length perml0 
  end

fun not_automorphic_pb (shape1,shape2) = 
  not_automorphic shape1 andalso not_automorphic shape2

(* -------------------------------------------------------------------------
   Nauty algorithm
   ------------------------------------------------------------------------- *)

val nauty_failure = ref false
val nauty_limit = 64

fun io_neighbors graph x =
  [inneighbor_of blue graph x,
   inneighbor_of red graph x,
   neighbor_of blue graph x,
   neighbor_of red graph x]

fun string_of_partition part = 
  String.concatWith "|" (map (String.concatWith " " o map its) part)

(* slow *)  
fun gather_colors colorv neighl =
  dlist (count_dict (dempty Int.compare) 
    (map (fn x => Array.sub(colorv,x)) neighl))
 
fun gather_iocolors colorv ioneighl = 
  map (gather_colors colorv) ioneighl

val charac_cmp = cpl_compare Int.compare
  (list_compare (list_compare (cpl_compare Int.compare Int.compare)))

fun decompose acc l = case l of
    [] => []
  | a :: m => (a,rev acc @ m) :: decompose (a :: acc) m 

fun refine_partition acc partition = case partition of
    [] => raise ERR "refine_partition" "all elements are colored differently"
  | [a] :: m => refine_partition ([a] :: acc) m
  | l :: m => map (fn (x,y) => rev acc @ [[x]] @ [y] @ m)              
              (decompose [] l)

fun unify_partitions graph graphsize partl = case partl of
    [] => []
  | [a] => [a]
  | _ => 
    let
      fun f x = mat_permute (graph,graphsize) (mk_permf (List.concat x))
      val mpartl = map (fn x => (f x, x)) partl
      val d = dnew (mat_compare_fixedsize graphsize) mpartl    
    in
      map snd (dlist d)
    end

fun colorv_of graphsize partition =
  let
    val cvl = distrib (number_fst 0 partition)
    val colorv = Array.array (graphsize,0)
    fun g (c,v) = Array.update (colorv,v,c)
    val _ = app g cvl
 in
   colorv
 end

fun equitable_partition_aux graphsize ioneighl partition =
  let val ncolor = length partition in
  if ncolor = graphsize then partition else
  let
    val colorv = colorv_of graphsize partition
    fun f (x,ioentry) = 
      ((Array.sub (colorv,x), gather_iocolors colorv ioentry), x)
    val characl1 = map f ioneighl
    val d = dregroup charac_cmp characl1
    val newncolor = dlength d
    val newpartition = map snd (dlist d) 
  in
    if newncolor < ncolor then 
      raise ERR "equitable_partition_aux" 
        (string_of_partition partition ^ " "  ^
         string_of_partition newpartition)
    else if newncolor = graphsize orelse newncolor = ncolor then
      newpartition
    else equitable_partition_aux graphsize ioneighl newpartition
  end
  end
  
fun equitable_partition graph =
  let
    val graphsize = mat_size graph
    val vertexl = List.tabulate (graphsize,I)
    val ioneighl = map_assoc (io_neighbors graph) vertexl
  in
    equitable_partition_aux graphsize ioneighl [vertexl]
  end

fun refine_partition_loop limit graph ioneighl partl = 
  if length partl > limit then (incr level2; nauty_failure := true;
                                first_n limit partl) 
  else
  let
    val graphsize = mat_size graph
    val partl1 = List.concat (map (refine_partition []) partl)
    val partl2 = map (equitable_partition_aux graphsize ioneighl) partl1
    val partl3 = unify_partitions graph graphsize partl2
    val (partl4,partl5) = partition (fn x => length x = graphsize) partl3
    val newlimit = limit - length partl4
  in
    if null partl5 
    then partl4 
    else partl4 @ refine_partition_loop newlimit graph ioneighl partl5
  end

(* warning: limited to "limit" partitions, 
   some partition might give the same graph *)
fun nauty_partition limit graph =
  let
    val graphsize = mat_size graph
    val vertexl = List.tabulate (graphsize,I)
    val ioneighl = map_assoc (io_neighbors graph) vertexl
    val part = equitable_partition_aux graphsize ioneighl [vertexl]
  in
    if length part = graphsize then [part] else 
    refine_partition_loop limit graph ioneighl [part]
  end

fun normalize_nauty graph =
  let 
    val _ = incr level1
    val graphsize = mat_size graph
    fun f x = mat_permute (graph,graphsize) (mk_permf x)
    val partl = nauty_partition nauty_limit graph
  in
    case partl of [part] => f (List.concat part) | _ =>
      let 
        val perml0 = map List.concat partl
        val matl = map f perml0
      in
        hd (dict_sort (mat_compare_fixedsize graphsize) matl)
      end
  end
  
fun normalize_nauty_safe graph = 
  let 
    val _ = nauty_failure := false
    val r = normalize_nauty graph
  in
    if !nauty_failure then raise ERR "normalize_nauty_safe" "" else r
  end
    
(* 
load "ramsey"; open aiLib kernel ramsey;
val x = random_shape 5 1;
val y = mat_to_edgecl x;
val l = equitable_partition x;
*)

(* -------------------------------------------------------------------------
   Test if a shape is a subgraph of a bigger graph
   ------------------------------------------------------------------------- *)
   
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
  
fun subsets_of_size n l =  subsets_of_size_faster n (l, length l)

fun subcoloring_aux size shape1 shape2 i j = 
  if Array2.sub (shape1,i,j) <> 0 andalso 
     Array2.sub (shape1,i,j) <> Array2.sub (shape2,i,j)
  then false
  else
  if j >= size - 1 then 
    if i >= size - 1 then true 
    else subcoloring_aux size shape1 shape2 (i+1) 0
  else subcoloring_aux size shape1 shape2 i (j+1)

fun subcoloring size shape1 shape2 = 
  subcoloring_aux size shape1 shape2 0 0;

fun keep_only color graph = 
  mat_tabulate (mat_size graph,
    fn (i,j) => if mat_sub (graph,i,j) = color then 1 else 0)

fun has_shape_wcedge graph ((i,j),color) =
  let 
    val shapesize = if color = blue then !blue_size_glob else !red_size_glob
    val supershape_arr = if color = blue 
       then !blue_supershapes_glob else !red_supershapes_glob
    val unigraph = keep_only color graph
    val vertexl = List.tabulate (mat_size unigraph, I)
    val l0 = filter (fn x => not (mem x [i,j])) vertexl
    val l1 = subsets_of_size (shapesize-2) l0
    fun f subset =
      let 
        val sigma = mk_permf (i :: j :: subset)
        (* todo: avoid this intermediate representation *)
        val candshape = mat_permute (unigraph,shapesize) sigma
        val entry = shape_to_int_fixedsize candshape
      in
        Array.sub (supershape_arr,entry)
        handle Subscript => raise ERR "has_shape_wcedge" (its entry ^ " " ^ its 
           (Array.length supershape_arr))
      end
  in
    exists f l1
  end;

(* -------------------------------------------------------------------------
   Test isomorphism
   ------------------------------------------------------------------------- *)
    
fun is_iso graph =     
  let val graphid = zip_mat (normalize_nauty graph) in
    if emem graphid (!isod_glob)   
    then true
    else (isod_glob := eadd graphid (!isod_glob); false)
  end

(* -------------------------------------------------------------------------
   Unit propagation
   ------------------------------------------------------------------------- *)

fun propagate_one graph undecl edgel = case edgel of 
    [] => SOME (graph,rev undecl)
  | edge :: m => 
    let 
      val blueext = mat_add (edge,blue) graph 
      val redext = mat_add (edge,red) graph
      val blueb = has_shape_wcedge blueext (edge,blue)
      val redb = has_shape_wcedge redext (edge,red) 
    in
      if blueb andalso redb then NONE
      else if blueb then propagate_one redext undecl m
      else if redb then propagate_one blueext undecl m
      else propagate_one graph (edge :: undecl) m
    end
   
fun propagate graph edgel =
   case propagate_one graph [] edgel of 
     NONE => NONE
   | SOME (graph,newedgel) => 
     if newedgel = edgel then SOME graph else propagate graph newedgel

(* -------------------------------------------------------------------------
   Test if a graph has cycle
   ------------------------------------------------------------------------- *)

fun neighbor color m x = 
  let fun test y = mat_sub (m,x,y) = color in
    filter test (List.tabulate (mat_size m,I))
  end

fun mat_to_neigh color m = Vector.tabulate (mat_size m, neighbor color m);

fun has_cycle color m =
  let
    val initneighv = mat_to_neigh color m
    val initindexl = List.tabulate (mat_size m,I)
    fun loop neighv indexl =
      let 
        val (reml,newindexl) =
          partition (fn x => null (Vector.sub(neighv,x))) indexl
      in
        if null newindexl then false else
        if null reml then true else 
        let val newneighv = Vector.map 
          (fn l => filter (fn x => not (mem x reml)) l) neighv 
        in 
          loop newneighv newindexl
        end
      end
  in
    loop initneighv initindexl
  end
    
fun random_shape_nocycle n color = 
  let val r = random_shape n color in 
    if has_cycle color r then random_shape_nocycle n color else r
  end
  
(* -------------------------------------------------------------------------
   Order in which the vertices should be colored
   ------------------------------------------------------------------------- *)

fun pairbelowy y = List.tabulate (y+1,fn x => (x,y))

fun search_order_undirected size = 
  let 
    val search_order0 = List.concat (List.tabulate (size,fn y => pairbelowy y))
  in
    filter (fn (x,y) => x <> y) search_order0
  end  

fun search_order size = List.concat 
  (map (fn (x,y) => [(x,y),(y,x)]) (search_order_undirected size))

fun search_order_linear size = 
  filter (fn (x,y) => x <> y)
  (cartesian_product (List.tabulate (size,I)) (List.tabulate (size,I)))


fun next_edge_aux graphsize graph edgel = case edgel of
    [] => NONE
  | (i,j) :: m => 
    if i >= graphsize orelse j >= graphsize then SOME (i,j) 
    else if mat_sub (graph,i,j) = 0 then SOME (i,j)
    else next_edge_aux graphsize graph m
  
fun next_edge graph = next_edge_aux (mat_size graph) graph (!edgel_glob)      

fun blank_edges graphsize graph edgel = case edgel of
    [] => []
  | (i,j) :: m => 
    if i >= graphsize orelse j >= graphsize then [] else 
      if mat_sub (graph,i,j) = 0 
      then (i,j) :: blank_edges graphsize graph m
      else blank_edges graphsize graph m

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

fun add_break () = if !counter >= 1000 then log "" else () 
fun stats () = 
  (
  log ("graphs: " ^ its (elength (!isod_glob)) ^ ", " ^ its (!level1));
  if !level2 <> 0 then log ("norm_failure: " ^ its (!level2)) else ()
  )
  
fun search_end grapho = case grapho of 
    NONE => (add_break (); log (if !sat_flag then "sat" else "unsat"); 
    stats (); (if !sat_flag then false else true)) 
  | SOME graph => (add_break (); log "sat"; 
      log (string_of_graph graph); stats(); false)
    
fun search_loop path = 
  case path of 
    [] => search_end NONE
  | (graph, []) :: parentl => search_loop parentl
  | (graph, color :: colorm) :: parentl =>    
    (
    case next_edge graph of
      NONE => if !continue_flag 
              then (sat_flag := true;
                    log (string_of_graph graph);
                    search_loop ((graph,[]) :: parentl))
              else search_end (SOME graph)
    | SOME edge =>
      let 
        fun f () = its (fst edge) ^ "," ^ its (snd edge) ^ ":" ^ its color
        val candgraph = mat_add (edge,color) graph 
        fun backtrack () = search_loop ((graph,colorm) :: parentl)
      in
        debugf "split: " f (); test_timer ();
        if has_shape_wcedge candgraph (edge,color)
          then (debug "conflict"; backtrack ()) else
        (
        case propagate candgraph 
          (blank_edges (mat_size candgraph) candgraph (!edgel_glob)) of
          NONE => (debug "pconflict"; backtrack ())
        | SOME propgraph =>
          if is_iso propgraph then (debug "iso"; backtrack ()) else
          let 
            val child = (propgraph,[blue,red])
            val newparentl = (graph,colorm) :: parentl
          in
            search_loop (child :: newparentl)
          end
        )
      end
   )

fun search size =
  let 
    val _ = init_timer ()
    val _ = isod_glob := eempty IntInf.compare
    val _ = edgel_glob := search_order_linear size
    val _ = log ("edge order: " ^ string_of_edgel (!edgel_glob))
    val _ = sat_flag := false
    val path = [(mat_tabulate (1, fn (i,j) => 0),[blue,red])]
  in
    search_loop path
  end

(* -------------------------------------------------------------------------
   Graph representations: set of edges, neighbors, adjacency matrices
   ------------------------------------------------------------------------- *)

fun edgecl_to_mat_fixedsize size edgecl =
  let 
    val edgel = map fst edgecl
    val edged = dnew (cpl_compare Int.compare Int.compare) edgecl
    fun f (i,j) = case dfindo (i,j) edged of NONE => 0 | SOME c => c 
  in
    mat_tabulate (size, f)
  end  

(* -------------------------------------------------------------------------
   Problems
   ------------------------------------------------------------------------- *)

fun read_edgel s =
  map pair_of_list
  (mk_batch 2 (map string_to_int (String.tokens (not o Char.isDigit) s)))

fun read_cnf file =
  let 
    val sl = readl file
    val reds = List.nth (sl,5)
    val blues = List.nth (sl,6)
  in
    ((edgel_to_shape (read_edgel blues), edgel_to_shape (read_edgel reds)),
     false)
  end
  
fun string_of_pbr (((x,y),b),(bunsat,n)) = 
  String.concatWith " || "
  [string_of_shape x, szip_mat x, if is_ackset x then "set" else "...",
   string_of_shape y, szip_mat y, if is_ackset y then "set" else "...",
   if b then "undirected" else "directed", 
   if bunsat then "unsat" else "sat", its n];  
  
(* -------------------------------------------------------------------------
   Shape tools
   ------------------------------------------------------------------------- *)

fun deduplicate_shapel shapel =
  let
    val l1 = map normalize_nauty_safe shapel
    val l2 = map swap (map_assoc shape_to_int l1)
    val d = dregroup Int.compare l2
    val l3 = map (fn (a,b) => hd b) (dlist d)  
 in
   l3
 end

fun all_undirected_shapes size = 
  let 
    val edgel = search_order_undirected size 
    val edgecll = cartesian_productl (map (fn x => [(x,0),(x,1)]) edgel)
    val edgecll' = filter (fn l => not (all (fn (_,c) => c = 0) l)) edgecll
    val matl = map edgecl_to_mat edgecll'
  in
    map symmetrify matl
  end
  
fun reduce_mat m = 
  let 
    val edgecl = mat_to_edgecl m
    val vertexl = mk_fast_set Int.compare 
      (List.concat (map (fn ((a,b),_) => [a,b]) edgecl))
  in
    mat_permute (m, length vertexl) (mk_permf vertexl)
  end 

fun directed_shapes shape =
  let 
    val edgecl = mat_to_edgecl_undirected shape
    fun f ((i,j),c) = [[((i,j),c)],[((j,i),c)],[((i,j),c),((j,i),c)]]
    val dishapel0 = map List.concat (cartesian_productl (map f edgecl))
    val dishapel1 = map edgecl_to_mat dishapel0
    val dishapel2 = filter (not o has_cycle 1) dishapel1
  in
    deduplicate_shapel dishapel2
  end

fun create_pbl_maxsize shapesize =
  let
    val shapel1 = all_undirected_shapes shapesize
    val shapel2 = deduplicate_shapel shapel1
    val shapel3 = map (normalize_nauty o reduce_mat) shapel2
    val shapel4 = map_assoc directed_shapes shapel3
    val pbl = cartesian_product shapel4 shapel4
    fun fii (x,y) = (x,y) (* (shape_to_int x, shape_to_int y) *)
    fun f ((u1,d1l),(u2,d2l)) = 
      (fii (u1,u2), map fii (cartesian_product d1l d2l))
  in
    map f pbl
  end

fun create_pbl_same_maxsize shapesize =
  let
    val shapel1 = all_undirected_shapes shapesize
    val shapel2 = deduplicate_shapel shapel1
    val shapel3 = map (normalize_nauty o reduce_mat) shapel2
    val shapel4 = map_assoc directed_shapes shapel3
    val pbl = map (fn x => (x,x)) shapel4
    fun fii (x,y) = (x,y) (* (shape_to_int x, shape_to_int y) *)
    fun f ((u1,d1l),(u2,d2l)) = 
      (fii (u1,u2), map fii (cartesian_product d1l d2l))
  in
    map f pbl
  end

(* -------------------------------------------------------------------------
   All supershapes of multiples shape
   ------------------------------------------------------------------------- *)

fun isomorphic_shapes shape =
  let
    val shapesize = Int.min (Array2.dimensions shape)
    val perml = permutations (List.tabulate (shapesize,I))
    val permfl = map mk_permf perml
    val shapel = map (mat_permute (shape,shapesize)) permfl
    val shaped = enew (mat_compare_fixedsize shapesize) shapel
    val _ = log (its (elength shaped) ^ " isomorphic variants")
  in
    elist shaped
  end

fun supershapes_one_aux size edgecl =
  let 
    val edgel = map fst edgecl
    val edgel1 = search_order size 
    val uncolored = filter (fn x => not (mem x edgel)) edgel1
    val l1 = cartesian_productl (map (fn x => [(x,0),(x,1)]) uncolored)
    val l2 = map (fn x => edgecl @ x) l1
    val il = map (fn x => shape_to_int_fixedsize 
       (edgecl_to_mat_fixedsize size x)) l2
  in
    il
  end

fun supershapes_one size shape = 
  supershapes_one_aux size (mat_to_edgecl shape)
  
fun supershapes shape = 
  let 
    val shapesize = mat_size shape
    val isoshapel = isomorphic_shapes shape
    val a = Array.array (int_pow 2 (shapesize * (shapesize - 1)), false)
    val i = ref 0
    fun f shape = 
      let val il = supershapes_one shapesize shape in
        app (fn x => (
          Array.update (a,x,true) handle Subscript => 
          raise ERR "supershapes" (its x); incr i)) il
      end
      
  in
    app f isoshapel; a
  end

(* -------------------------------------------------------------------------
   Experiment
   ------------------------------------------------------------------------- *)

fun init_supershapes (blueshape,redshape) =
  let
    val _ = print_endline ("blue shape: " ^ string_of_shape blueshape)
    val _ = blue_supershapes_glob := supershapes blueshape
    val _ = print_endline ("red shape:  " ^ string_of_shape redshape)
    val _ = red_supershapes_glob := supershapes redshape
    val _ = blue_size_glob := mat_size blueshape
    val _ = red_size_glob := mat_size redshape
  in
    ()
  end
  
fun search_each_size ((blueshape,redshape),symflag) =
  let
    val _ = symmetry_flag := symflag
    val (_,t) = add_time init_supershapes (blueshape,redshape)
    val _ = print_endline ("initializing supershapes: " ^ rts_round 2 t)
    val initsize = Int.max (mat_size blueshape, mat_size redshape) 
    fun loop csize =
      let 
        val _ = log ("search with graph size: " ^ its csize)  
        val b = search csize
        val _ = print_endline ""
      in
        if b then (true,csize) else loop (csize + 1)
      end
      handle RamseyTimeout => 
        (add_break (); log "timeout"; stats(); (false,csize)) 
  in
    loop initsize 
  end
  
fun search_one_size size ((blueshape,redshape),symflag) =
  let
    val _ = symmetry_flag := symflag
    val (_,t) = add_time init_supershapes (blueshape,redshape)
    val _ = print_endline ("initializing supershapes: " ^ rts_round 2 t)
    fun loop csize =
      let 
        val _ = log ("search with graph size: " ^ its csize)  
        val b = search csize
        val _ = print_endline ""
      in
        if b then (true,csize) else (false,csize)
      end
      handle RamseyTimeout => 
        (add_break (); log "timeout"; stats(); (false,0)) 
  in
    loop size 
  end  
  
(*
load "ramsey"; open aiLib kernel ramsey;
continue_flag := true; (* todo add final graph to set *)
shuffle_flag := true;
val edgecl = map_assoc (fn _ => 1) 
  [(0,2),(1,3),(2,0),(2,4),(3,1),(3,4),(4,2),(4,3)];
val graph = edgecl_to_mat edgecl;  
val r1 = search_each_size ((graph,graph),true);

val edgecl = map_assoc (fn _ => 1) 
  [(0,1),(1,0),(1,2),(2,1),(2,0),(0,2)];
val graph = edgecl_to_mat edgecl;  
val r1 = search_each_size ((graph,graph),true);

*)  

(* -------------------------------------------------------------------------
   Parallel execution
   ------------------------------------------------------------------------- *)

fun ramseyspec_fun param (brshape,symflag) =
   let
     val (r,t) = add_time search_each_size (brshape,symflag)
     val _ = log ("problem time: " ^ rts_round 2 t)
   in
     r
   end 

val ramseyspec : 
  (unit, ((mat * mat) * bool), (bool * int)) extspec =
  {
  self_dir = selfdir,
  self = "ramsey.ramseyspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = ramseyspec_fun,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = 
    let fun f file ((m1,m2),b) = 
      writel file [szip_mat m1 ^ " " ^ szip_mat m2 ^ " " ^ bts b] 
    in f end,
  read_arg = 
    let fun f file = 
      let val (s1,s2,s3) = triple_of_list 
        (String.tokens Char.isSpace (hd (readl file))) 
      in 
        ((sunzip_mat s1,sunzip_mat s2),string_to_bool s3)
      end
    in f end,
  write_result = 
     let fun f file (b,i) = 
        writel file [bts b ^ " " ^ its i] 
     in f end,
  read_result = 
    let fun f file = 
      let val (s1,s2) = split_string " " (hd (readl file)) in 
        (string_to_bool s1, string_to_int s2)
      end
    in f end
  }

fun parallel_ramsey ncore expname pbl =
  let
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = mkDir_err dir
    val _ = smlExecScripts.buildheap_dir := dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
    val (rl,t) = add_time (parmap_queue_extern ncore ramseyspec ()) pbl
    val l = combine (pbl,rl)
    fun f (((m1,m2),b),(rb,rn)) = 
      string_of_graph m1 ^ "\n" ^
      string_of_graph m2 ^ "\n" ^
      String.concatWith " " [szip_mat m1,szip_mat m2,bts b,
        if rb then "sat" else "unsat", its rn] 
  in
    writel (dir ^ "/log") ["time: " ^ rts t];
    writel (dir ^ "/results") (map f l);
    l
  end
 
  
end (* struct *) 

(*
load "ramsey"; open aiLib kernel ramsey;
val filel = listDir (selfdir ^ "/dr100");
val cnfl = map (fn x => selfdir ^ "/dr100/" ^ x) 
  (filter (fn x => String.isSuffix "_cnf.p" x) filel);
val pbl = map read_cnf cnfl;

val rl = parallel_ramsey 32 "linsearch" pbl;
length rl;
*)

(*
load "ramsey"; open aiLib kernel ramsey;
val pbl = create_pbl_same_maxsize 5;
val pbl1 = map (fn (a,b) => (a,true) :: 
  map_assoc (fn _ => false) (filter not_automorphic_pb b)) pbl;
val pbl2 = filter (fn x => length x >= 3) pbl1;
val pbl3 = List.concat pbl2; length pbl3;
val r = parallel_ramsey 64 "notauto" pbl3;
val d = dnew (triple_compare mat_compare

fun test pbdi =
  let 
    val y = map search_each_size (map_assoc (fn _ => false) pbdi)
    val l = mk_fast_set Int.compare (map snd (filter fst y))
  in
    length l >= 2
  end;
    
val r = valOf (List.find test (shuffle pbl3));


fun mat_compare_aux size a1 a2 i j = 
  case Int.compare (Array2.sub (a1,i,j),Array2.sub (a2,i,j)) of
      EQUAL => if j >= size - 1 then 
                 if i >= size - 1 
                 then EQUAL 
                 else mat_compare_aux size a1 a2 (i+1) 0
               else mat_compare_aux size a1 a2 i (j+1)
    | r => r;

fun mat_compare_fixedsize size (a1,a2) = 
  mat_compare_aux size a1 a2 0 0;

fun mat_compare (a1,a2) = 
  case Int.compare (mat_size a1, mat_size a2) of
    EQUAL => mat_compare_aux (mat_size a1) a1 a2 0 0
  | x => x;
  
val cmp = cpl_compare (cpl_compare mat_compare mat_compare) bool_compare;  
val rd = dnew cmp r;

val pbl2r = map (map_assoc (fn x => dfind x rd)) pbl2;

fun testr l = 
  let val l' = filter (fn x => fst (snd x)) l in
    length (mk_fast_set (snd_compare (snd_compare Int.compare)) l') >= 2
  end;
  
val pbl2rempty = filter testr pbl2r;  


  
 

fun szip_mat m = IntInf.toString (zip_mat m);
fun sunzip_mat s = unzip_mat (valOf (IntInf.fromString s));



fun string_of_pbl pbl = String.concatWith "\n" (map string_of_pbr pbl) ^ "\n";

writel "ramsey_notauto_full" (map string_of_pb r);
writel "ramsey_notauto_counter" (map string_of_pbl pbl2rempty);

fun contain_ackset (((x,y),b),(bunsat,n)) = is_ackset x andalso is_ackset y;

fun testrset l = 
  let val l' = filter contain_ackset l in
    length (mk_fast_set (snd_compare (snd_compare Int.compare)) l') >= 2
  end;

val pbl2rset = filter testrset pbl2rempty;  

fun string_of_pbl_set pbl = String.concatWith "\n" (map string_of_pbr
  (filter contain_ackset pbl)) ^ "\n";

writel "ramsey_notauto_counter_set" (map string_of_pbl_set pbl2rset);




fun f pbdi =
  let val y = map search_each_size (map_assoc (fn _ => false) pbdi) in
    combine (pbdi,y)
  end;

val r2 = f r;
val d2 = dregroup (cpl_compare bool_compare Int.compare) (map swap (snd r2));
val l2 = map (hd o snd) (dlist d2);
fun p (x,y) = print_endline (string_of_shape x ^ " || " ^ string_of_shape y);
app p l2;

val rl = parallel_ramsey 32 "nocache" (rev cnfl);
length rl;
*)

(*

shape: 0 -> 1 2 3, 1 -> 2 3, 2 -> 3, 3 -> 
24 isomorphic variants
red shape:  0 -> 2 3, 1 -> 3, 2 -> 1 3, 3 -> 
*)


