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

val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)

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


val undirected_flag = ref false
(* flags conspiring to output all models *)
val continue_flag = ref false
val sat_flag = ref false
val degree_flag = ref false
val max_blue_degree = ref 0
val max_red_degree = ref 0
val iso_flag = ref true
val sbl_flag = ref false
val graphl = ref []
val conel = ref []


(* -------------------------------------------------------------------------
   Logging
   ------------------------------------------------------------------------- *)

val disable_log = ref false

val logfile = ref (selfdir ^ "/log")
val store_log = ref false

fun log s = 
  if !disable_log then () 
  else if !store_log then (print_endline s; append_endline (!logfile) s)
  else print_endline s

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val blue = 1
val red = 2
val edgel_glob = ref []
val blue_size_glob = ref 0
val red_size_glob = ref 0
val limit_glob = 
  (if abstract_time > 0 then SOME abstract_time else NONE, 
   if real_time > 0.0 then SOME (Time.fromReal real_time) else NONE)
val timer = ref (Timer.startRealTimer ())
val isod_glob = ref (eempty IntInf.compare)

(* -------------------------------------------------------------------------
   Timer and statistics
   ------------------------------------------------------------------------- *)

exception RamseyTimeout;

val sat_n = ref 0
val prop_timer = ref 0.0
val iso_timer = ref 0.0
val iso_timer2 = ref 0.0
val prop_counter = ref 0
val prop_small_counter = ref 0
val prop_conflict_counter = ref 0
val iso_counter = ref 0
val norm_failure = ref 0
val degree_counter = ref 0
val degree_timer = ref 0.0
val degree_conflict_counter = ref 0

val other_counter = ref 0
val other_timer = ref 0.0


fun init_timer () =
  (
  graphl := [];
  conel := [];
  sat_n := 0;
  prop_counter := 0;
  prop_small_counter := 0;
  prop_conflict_counter := 0;
  prop_timer := 0.0;
  iso_counter := 0;
  iso_timer := 0.0;
  iso_timer2 := 0.0;
  norm_failure := 0;
  other_counter := 0;
  other_timer := 0.0;
  degree_counter := 0;
  degree_conflict_counter := 0;
  degree_timer := 0.0; 
  timer := Timer.startRealTimer ()
  )

fun test_timer () =
  let
    val _ = incr prop_counter
    val _ = if !prop_counter mod 1000 = 0 then print "." else ()
    val _ = case fst (limit_glob) of NONE => () | SOME ti => 
      if !prop_counter > ti then raise RamseyTimeout else ()
    val _ = case snd (limit_glob) of NONE => () | SOME tr => 
      if Timer.checkRealTimer (!timer) > tr then raise RamseyTimeout else ()
  in
    ()
  end

fun stats () = 
  (  
  log ("prop: " ^ its (!prop_counter) ^ " calls, " ^ 
                  its (!prop_small_counter) ^ " propagations, " ^ 
                  its (!prop_conflict_counter) ^ " conflicts, " ^ 
                  rts_round 6 (!prop_timer) ^ " seconds");
  log ("iso: " ^ its (!iso_counter) ^ " calls, " ^ 
       its ((!iso_counter) - (elength (!isod_glob))) ^ " conflicts, " ^
       rts_round 6 (!iso_timer) ^ " seconds, " ^
       rts_round 6 (!iso_timer2) ^ " seconds"
       );
  log ("degree: " ^ its (!degree_counter) ^ " calls, " ^ 
                    its (!degree_conflict_counter) ^ " conflicts, " ^ 
                    rts_round 6 (!degree_timer) ^ " seconds");       
  log ("other: " ^ its (!other_counter) ^ " calls");    
  if !sat_n > 0 andalso !continue_flag
    then log ("models: " ^ its (!sat_n)) else ();
  if !norm_failure > 0 
    then log ("norm: " ^ its (!norm_failure)) else ()
  )

(* -------------------------------------------------------------------------
   Adjacency matrix representation
   ------------------------------------------------------------------------- *)

type mat = int Array2.array
fun mat_sub (m,i,j) = Array2.sub (m,i,j)
fun mat_update (m,i,j,x) = Array2.update(m,i,j,x)

fun mat_tabulate (n,f) = Array2.tabulate Array2.RowMajor (n,n,f)
fun mat_appi f m = 
  let val range = {base=m,row=0,col=0,nrows=NONE,ncols=NONE} in
    Array2.appi Array2.RowMajor f range
  end

fun mat_app f m = Array2.app Array2.RowMajor f m

val edge_compare = cpl_compare Int.compare Int.compare  


fun size_of_zip l =
  let val ln = length l in
    valOf (List.find (fn x => x * (x - 1) = ln) (List.tabulate (100,I)))
  end
  
local open IntInf in

fun zip_mat_directed m =
  let val r = ref 1 in
    mat_appi (fn (i,j,x) => if i = j then () else 
                            r := !r * 3 + IntInf.fromInt x) m; !r
  end
 
fun zip_mat_undirected m =
  let val r = ref 1 in
    mat_appi (fn (i,j,x) => if FixedInt.>= (i,j) then () else 
                            r := !r * 3 + IntInf.fromInt x) m; !r
  end  

(* figure out whcih index are written 
   when using zip_mat_undirected *) 
  
fun zip_mat m = 
  if !undirected_flag then zip_mat_undirected m else zip_mat_directed m 
  
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

fun random_full_mat size = 
  mat_tabulate (size,fn (a,b) => if a=b then 0 else random_int (1,2));

fun mat_size m = 
  let val (a,b) = Array2.dimensions m in
    if a = b then a else raise ERR "mat_size" ""
  end 
  
fun mat_copy graph = 
  let fun f (i,j) = mat_sub (graph,i,j) in
    mat_tabulate (mat_size graph, f)
  end
  
  
fun random_shape size color =
   mat_tabulate (size,fn (a,b) => if a=b then 0 else 
    if random_real () < 0.5 then 0 else color)

fun symmetrify m = 
  mat_tabulate (mat_size m, fn (a,b) => 
  if a=b then 0 else if a < b then mat_sub (m,a,b) else mat_sub (m,b,a));

fun random_symmat size = symmetrify (random_mat size);
 
fun random_full_symmat size = symmetrify (random_full_mat size); 
 
fun matK size = 
  mat_tabulate (size,fn (a,b) => if a=b then 0 else 1);
 
fun matKn size n = 
  mat_tabulate (size + 1, fn (a,b) => 
    if (a = size andalso b >= n) orelse 
       (b = size andalso a >= n) orelse (a=b) 
    then 0 else 1
       );

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

(* assumes shape contains 1 and 0s and is not too big *)    
fun shape_to_int_fixedsize m = 
  if !undirected_flag then 
  let val r = ref 0 (* can start at zero because all the same size *) in
    mat_appi (fn (i,j,x) => if i <= j then () else r := !r * 2 + x) m; !r
  end
  
  else
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
  handle Subscript => raise ERR "neighbor_of" ""
  
fun commonneighbor_of color graph (a,b) = 
  let 
    val vertexl = List.tabulate (mat_size graph,I)
    fun test y = (mat_sub (graph,a,y) = color andalso 
                  mat_sub (graph,b,y) = color)
  in
    filter test vertexl
  end
  handle Subscript => raise ERR "commonneighbor_of" ""  


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
  
fun named_neighbor color graph = 
  filter (not o null o snd) (number_fst 0 (all_neighbor color graph))  
  
fun string_of_graph graph = 
  let fun f (i,l) = its i ^ "-" ^ String.concatWith "_" (map its l) in
    String.concatWith " " (map f (named_neighbor blue graph)) ^ " | " ^
    String.concatWith " " (map f (named_neighbor red graph))
  end

fun string_of_bluegraph_undirected graph = 
  let 
    val l1 = named_neighbor blue graph
    fun g (i,l) = (i, filter (fn x => x > i) l)
    val l2 = map g l1
    val l3 = filter (not o null o snd) l2
    fun f (i,l) = its i ^ "-" ^ String.concatWith "_" (map its l) 
  in
    String.concatWith ", " (map f l3)
  end
  
fun string_of_bluegraph_directed graph = 
  let fun f (i,l) = its i ^ "-" ^ String.concatWith "_" (map its l) in
    String.concatWith ", " (map f (named_neighbor blue graph))
  end

fun string_of_bluegraph graph =
  if !undirected_flag 
  then string_of_bluegraph_undirected graph
  else string_of_bluegraph_directed graph

(* -------------------------------------------------------------------------
   Order in which the vertices should be colored
   ------------------------------------------------------------------------- *)

fun pairbelowy y = List.tabulate (y+1,fn x => (x,y))

fun search_order_undirected size = 
  let val search_order0 = 
    List.concat (List.tabulate (size,fn y => pairbelowy y))
  in
    filter (fn (x,y) => x <> y) search_order0
  end  

fun search_order size = List.concat 
  (map (fn (x,y) => [(x,y),(y,x)]) (search_order_undirected size))

fun search_order_linear size = 
  filter (fn (x,y) => x <> y)
  (cartesian_product (List.tabulate (size,I)) (List.tabulate (size,I)))

fun search_order_linear_undirected size = 
  filter (fn (x,y) => x < y)
  (cartesian_product (List.tabulate (size,I)) (List.tabulate (size,I)))

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


fun edgecl_to_mat_size size edgecl =
  let 
    val edgel = map fst edgecl
    val edged = dnew (cpl_compare Int.compare Int.compare) edgecl
    fun f (i,j) = case dfindo (i,j) edged of NONE => 0 | SOME c => c 
  in
    mat_tabulate (size, f)
  end

local open IntInf in

fun zip_full m =
  let val r = ref 1 in
    mat_appi (fn (i,j,x) => 
      if FixedInt.>= (i,j) then () else 
      r := !r * 2 + IntInf.fromInt (if x = blue then 1 else 0)) m; !r
  end
  
fun zip_full_indices size =
  let 
    val m = mat_tabulate (size, fn _ => 0)
    val r = ref []
    fun f (i,j,x) = if FixedInt.>= (i,j) then () else r := (i,j) :: !r;
  in
    mat_appi f m;
    rev (!r)
  end  
  
fun unzip_full size mati =
  let 
    fun loop x = if x < 2 then [] else x mod 2 :: loop (x div 2) 
    val l1 = rev (loop mati)
    val l2 = zip_full_indices size
    val edgecl0 = combine (l2, map IntInf.toInt l1)
    val edgecl1 = map_snd (fn b => if b = 1 then blue else red) edgecl0
  in
    symmetrify (edgecl_to_mat_size size edgecl1)
  end
  
fun unzip_full_edgecl size mati =
  let 
    fun loop x = if x < 2 then [] else x mod 2 :: loop (x div 2) 
    val l1 = rev (loop mati)
    val l2 = zip_full_indices size
    val edgecl0 = combine (l2, map IntInf.toInt l1)
    val edgecl1 = map_snd (fn b => if b = 1 then blue else red) edgecl0
  in
    edgecl1
  end  
  
end (* local *)

(* 
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 20;
val m = random_full_symmat 11;
val i = zip_full m;
val m1 = unzip_full 11 i;
mat_compare (m,m1);
*)


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
   Properties of shapes
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
   Nauty algorithm
   ------------------------------------------------------------------------- *)

val nauty_failure = ref false
val nauty_limit = 64

fun io_neighbors graph x =
  if !undirected_flag 
  then [neighbor_of blue graph x, neighbor_of red graph x]
  else [inneighbor_of blue graph x,
        inneighbor_of red graph x,
        neighbor_of blue graph x,
        neighbor_of red graph x]

fun string_of_partition part = 
  String.concatWith "|" (map (String.concatWith " " o map its) part)

(* slow *)  

fun dpeek x d = Redblackmap.peek (d,x)

fun count_elements arr l =
  let
    fun countHelper [] = ()
      | countHelper (x::xs) = 
        (Array.update (arr, x, Array.sub(arr, x) + 1); countHelper xs)
  in
    countHelper l
  end

fun gather_colors numcolors colorv neighl =
  let
    val colorl = map (fn x => Array.sub(colorv,x)) neighl
    val countsArr = Array.array(numcolors,0)
    val _ = count_elements countsArr colorl
    fun f (color,occ,acc) = 
      if occ > 0 then (color,occ) :: acc else acc
  in
    Array.foldri f [] countsArr
  end
 
fun gather_iocolors numcolors colorv ioneighl = 
  map (gather_colors numcolors colorv) ioneighl

fun inv_cmp cmp (a,b) = cmp (b,a)
val inv_int_compare = inv_cmp Int.compare

val charac_cmp = cpl_compare Int.compare
  (list_compare (list_compare (cpl_compare inv_int_compare inv_int_compare)))

fun decompose acc l = case l of
    [] => []
  | a :: m => (a,rev acc @ m) :: decompose (a :: acc) m 

fun refine_partition_aux acc partition = case partition of
    [] => raise ERR "refine_partition" "all elements are colored differently"
  | [a] :: m => refine_partition_aux ([a] :: acc) m
  | l :: m => map (fn (x,y) => rev acc @ [[x]] @ [y] @ m)              
              (decompose [] l)

fun refine_partition partition = 
  refine_partition_aux [] partition


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
      ((Array.sub (colorv,x), gather_iocolors ncolor colorv ioentry), x)
    val characl1 = total_time iso_timer2 (map f) ioneighl
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
  if length partl > limit then (incr norm_failure; nauty_failure := true;
                                first_n limit partl) 
  else
  let
    val graphsize = mat_size graph
    val partl1 = List.concat (map refine_partition partl)
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
fun nauty_partition limit graph parttop =
  let
    val graphsize = mat_size graph
    val vertexl = List.tabulate (graphsize,I)
    val ioneighl = map_assoc (io_neighbors graph) vertexl
    val part = equitable_partition_aux graphsize ioneighl parttop
  in
    if length part = graphsize then [part] else 
    refine_partition_loop limit graph ioneighl [part]
  end
 
fun normalize_nauty_aux graph parttop =
  let
    val graphsize = mat_size graph
    fun f x = mat_permute (graph,graphsize) (mk_permf x)
    val partl = nauty_partition nauty_limit graph parttop
  in
    case partl of [part] => f (List.concat part) | _ =>
      let 
        val perml0 = map List.concat partl
        val matl = map f perml0
      in
        hd (dict_sort (mat_compare_fixedsize graphsize) matl)
      end
  end
 
fun normalize_nauty graph =
  normalize_nauty_aux graph [List.tabulate (mat_size graph,I)]
  
fun normalize_nauty_safe graph = 
  let 
    val _ = nauty_failure := false
    val r = normalize_nauty graph
  in
    if !nauty_failure then raise ERR "normalize_nauty_safe" "" else r
  end

(*
load "ramsey"; open aiLib kernel ramsey;
val x = symmetrify (random_shape 5 1);
val x = matK 5;
val isovl = iso_vertices x;
val part = [List.tabulate (5,I)];
val y1 =  refine_partition part;
val y2 = List.concat (map refine_partition y1);
val isoel = iso_edges x;
mat_to_edgecl x;
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

(* -------------------------------------------------------------------------
   Test isomorphism
   ------------------------------------------------------------------------- *)
    
fun is_iso_aux graph =
  let 
    (* val _ = debugf "graph: " string_of_graph graph *)
    val normgraph = normalize_nauty graph
    (* val _ = debugf "normgraph: " string_of_graph normgraph *)
    val graphid = zip_mat normgraph
    (* val _ = debugf "graphid: " IntInf.toString graphid *)
  in
    if emem graphid (!isod_glob)   
    then true
    else (isod_glob := eadd graphid (!isod_glob); false)
  end
  
fun is_iso graph =
  (incr iso_counter; total_time iso_timer is_iso_aux graph)


(* -------------------------------------------------------------------------
   Doubly-linked vector
   ------------------------------------------------------------------------- *)


(* returns a fucntion to undo the operation *)
fun dlv_del i dlv = 
  let 
    val ((predi,suci),_) = Vector.sub (dlv,i)
    val ((_,predf),_) = Vector.sub (dlv,!predi)
    (* val _ = debug ("2: " ^ its (!predi) ^ " " ^ its (!suci)) *)
    val ((sucb,_),_) = Vector.sub (dlv,!suci)
  in
    predf := !suci; sucb := !predi;
    fn () => (predf := i; sucb := i)
  end

fun dlv_fromlist dummy l = 
  let 
    val l1 = dummy :: (l @ [dummy])
    fun f i x = ((ref (i-1), ref (i+1)), x)
    val l2 = mapi f l1
  in
    Vector.fromList l2
  end
  
fun dlv_app f dlv = 
  let
    val last_index = Vector.length dlv - 1
    val first_index = (! o snd o fst) (Vector.sub (dlv,0)) 
    fun dlv_loop g start =
      if start = last_index then () else
      let 
        val ((_,nextref),x) = Vector.sub (dlv,start)
        val next = !nextref
      in
        g x; dlv_loop g next
      end
  in
    dlv_loop f first_index
  end


(* -------------------------------------------------------------------------
   Conversion between edges and variables
   ------------------------------------------------------------------------- *)

val convertv = Vector.fromList (search_order_undirected 50);
fun project x = Vector.sub (convertv,x) 
  handle Subscript => raise ERR "project" "";
fun id_pair (x,y) = 
  if x = y then raise ERR "id_pair" ""
  else if x < y then x + ((y * (y - 1)) div 2) else id_pair (y,x)

fun cts c = 
  if c = 1 then "b" 
  else if c = 2 then "r"
  else if c = 0 then "w"
  else raise ERR "cts_color" (its c)

fun ets (edgeid,c) = 
  let val (a,b) = project edgeid in
    its a ^ "-" ^ its b ^ ":" ^ cts c
  end
  
fun string_of_clausev clausev = 
  let fun f lit = ets (fst (fst lit), snd lit) in
    String.concatWith " " (map f (vector_to_list clausev))
  end
  
fun string_of_assignv assignv = 
  let 
    val l1 = map (! o fst) (vector_to_list assignv)
    val l2 = number_fst 0 l1
  in
    String.concatWith " " (map ets l2)
  end  

(* -------------------------------------------------------------------------
   Problem creation
   ------------------------------------------------------------------------- *)

fun clique_of_subset (subset,color) =
  let val pairl = all_pairs (dict_sort Int.compare subset) in
    map (fn x => (id_pair x, color)) pairl
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

fun clique_of_subset2 (subset,color) =
  let val pairl = all_pairs (dict_sort Int.compare subset) in
    map (fn x => (x, color)) pairl
  end

fun all_clauses2 size (bluesize,redsize) = 
  let
    val bluesubsetl = subsets_of_size bluesize (List.tabulate (size,I))
    val redsubsetl = subsets_of_size redsize (List.tabulate (size,I))
    val subsetl = map_assoc (fn _ => blue) bluesubsetl @
                  map_assoc (fn _ => red) redsubsetl
  in
    map clique_of_subset2 subsetl
  end  

fun reduce_clause edgecd acc clause = case clause of
    [] => SOME (rev acc)
  | (lit as ((i,j),color)) :: m => 
    let val newcolor = mat_sub (edgecd,i,j) in
      if newcolor = 0 then reduce_clause edgecd (lit :: acc) m
      else if color = newcolor then reduce_clause edgecd acc m else NONE
    end


local
  val colorglob = ref 0
  val acc_glob = ref ([] : (int list * ((int * int) * int) list) list);
  fun fadd_one (vl,el) vtop = 
    let val newlitl = map (fn v => ((v,vtop),!colorglob)) vl in
      acc_glob := (vtop :: vl, newlitl @ el) :: !acc_glob
    end
  fun fadd_loop (vl,el) start bound = 
    if start >= bound then () else
    (fadd_one (vl,el) start;  fadd_loop (vl,el) (start + 1) bound)
  fun fadd bound (vl,el) = fadd_loop (vl,el) (hd vl + 1) bound
  fun enum bound l = (acc_glob := []; app (fadd bound) l; !acc_glob)
  fun enum_n_aux bound n acc  = 
    if n <= 1 then acc else enum_n_aux bound (n-1) (enum bound acc)
in 
  fun enum_n bound n color = 
    (colorglob := color; map snd 
    (enum_n_aux bound n (List.tabulate (bound,fn x => ([x],[])))))
end

fun all_clauses2_faster size (bluesize,redsize) =
  enum_n size bluesize blue @ enum_n size redsize red

fun all_clauses3 size (bluesize,redsize) edgecd =
  List.mapPartial (reduce_clause edgecd []) 
  (all_clauses2_faster size (bluesize,redsize))

(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;
val (x,t) = add_time (all_clauses2 20) (4,5);
val (x',t') = add_time (all_clauses2_faster 24) (4,5);
*)

local
  fun fadd_one acc vl vtop = acc := (vtop :: vl) :: !acc
  fun fadd_loop acc vl start bound = 
    if start >= bound then () else
    (fadd_one acc vl start;  fadd_loop acc vl (start + 1) bound)
  fun fadd acc bound vl = fadd_loop acc vl (hd vl + 1) bound
  fun enum bound l = 
    let val acc = ref [] in app (fadd acc bound) l; !acc end
  fun enum_n_aux bound n acc  = 
    if n <= 0 then [[]] else 
    if n <= 1 then acc else enum_n_aux bound (n-1) (enum bound acc)
in 
  fun fixed_enum offset bound degree =
    enum_n_aux bound degree
      (List.tabulate (bound - offset,fn x => [x + offset]))
  fun stars_up edgecd csize dsize color maxdegree vertex = 
    let 
      val degree = maxdegree - 
        (length (neighbor_of color edgecd vertex) +
         (if color = blue then 1 else 0))
      val _ = if degree <= 0 then raise ERR "stars_up" "" else ()
      val l = fixed_enum csize (csize + dsize) degree
      fun f vl = map (fn x => ((vertex,x),color)) vl
      val clauses = map f l
    in
      clauses
    end
  fun stars_down edgecd csize dsize color maxdegree vertex = 
    let      
      val degree = maxdegree - 
        (length (neighbor_of color edgecd vertex) + 
         (if color = red then 1 else 0))
      val _ = if degree <= 0 then raise ERR "stars_down" "" else ()
      val l = fixed_enum 0 csize degree
      fun f vl = map (fn x => ((x,vertex),color)) vl
      val clauses = map f l
    in
      clauses
    end
  fun all_stars edgecd (bluedegree,reddegree) csize dsize = 
    let
      val cvl = List.tabulate (csize, I)
      val dvl = List.tabulate (dsize, fn x => x + csize)
    in
      List.concat 
        (map (stars_up edgecd csize dsize blue bluedegree) cvl @
         map (stars_up edgecd csize dsize red reddegree) cvl @
         map (stars_down edgecd csize dsize blue bluedegree) dvl @
         map (stars_down edgecd csize dsize red reddegree) dvl)
    end
end
  
  
  
(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 20;
val csize = 10;
val dsize = 14;
val edgecd = 
  symmetrify (
  mat_tabulate (csize + dsize, fn (i,j) => if i = j orelse 
  (i < csize andalso j >= csize) then 0 else random_int (1,2)));
val (x,t) = add_time (all_stars edgecd (12,15) 10) 14;
length x;

val lit_compare = cpl_compare edge_compare Int.compare;
val clause_compare = list_compare lit_compare;



val (x',t') = add_time (all_clauses2_faster 24) (4,5);
*)

(* -------------------------------------------------------------------------
   Moving clause list into efficient data structure
   ------------------------------------------------------------------------- *)

(* inefficient *)
val graph_glob = ref (Array2.array (1,1,0));
val isograph_glob = ref (Array2.array (1,1,0));

(* 1 in the graph means blue, 
   1 in the sat problem means not blue *)

fun add_clause (clause,(assignv,clausevv)) =
  let
    val cid = Vector.length clausevv
    val nvar = Vector.length assignv
    val maxvar = list_imax (map fst clause)
    val newassignv = 
      if maxvar < nvar then assignv else
      let val v = 
        Vector.tabulate (maxvar + 1 - nvar, fn i => (ref [], ref []))
      in
        Vector.concat [assignv,v]
      end
    fun f cvid (vid,color) = 
      let 
        val (l1,l2) = Vector.sub (newassignv, vid) 
        val l = if color = blue then l1 else l2
      in
        (* only the two first literals are watched *)
        if cvid <= 1 then l := (cid,cvid) :: !l else ()
      end
    val _ = appi f clause
    val newclausev = Vector.fromList clause
    val newclausevv = Vector.concat [clausevv,Vector.fromList [newclausev]]
  in
    (newassignv, newclausevv)
  end
  
fun add_clausel clausel (assignv,clausevv) = 
  foldl add_clause (assignv,clausevv) clausel

fun new_clausel clausel =
  let 
    val assignv = Vector.fromList []
    val clausevv = Vector.fromList []
  in
    add_clausel (map (map_fst id_pair) clausel) (assignv,clausevv)  
  end
  
  
fun transform_pb (assignv,clausevv) = 
  let 
    fun f1 (l1,l2) = (ref 0,(l1,l2))
    fun f2 x = (x, (ref 0, ref 1))
  in
    (Vector.map f1 assignv, Vector.map f2 clausevv)
  end


(*

  
val (_,t) = add_time (enum5 24) (fn _ => ());  
*)

(* -------------------------------------------------------------------------
   Additional symmetry breaking clauses
   ------------------------------------------------------------------------- *)

val fresh_var_counter = ref 0  
  
fun fresh_var () = 
  let val r = !fresh_var_counter in incr fresh_var_counter; r end

fun eq_clauses_one ((i,j),k) = 
  if i = k orelse j = k then NONE else
  let 
    val edge1 = (i,k)  
    val edge2 = (j,k)
    val eqv = (~1,fresh_var ())
  in
    SOME (((i,j),k),(eqv, [[(edge1,blue),(edge2,blue),(eqv,red)],
                           [(edge1,red),(edge2,red),(eqv,red)]]))
  end  

(* slightly too many clauses *)   
fun eq_clauses size =
  let
    val l0 = List.tabulate (size,I)
    val l1 = cartesian_product (all_pairs l0) l0
    val cmp = cpl_compare (cpl_compare Int.compare Int.compare) Int.compare
  in
    dnew cmp (List.mapPartial eq_clauses_one l1)
  end
  
fun sbl_clauses_aux d ((i,j),k) =
  if i = k orelse j = k then NONE else
  let 
    val l0 = filter (fn x => not (mem x [i,j])) (List.tabulate (k,I)) 
    val eql = map (fn x => fst (dfind ((i,j),x) d)) l0
  in
    SOME (map_assoc (fn _ => blue) eql @ 
          [((i,k),blue),((j,k),red)])
  end
  
fun sbl_clauses_aux2 size =
  let
    val _ = fresh_var_counter := (size * (size - 1)) div 2
    val l0 = List.tabulate (size,I)
    val l1 = cartesian_product (all_pairs l0) l0
    val d = eq_clauses size
    val l2 = List.concat (map (snd o snd) (dlist d))
  in
    l2 @ List.mapPartial (sbl_clauses_aux d) l1
  end
  
fun sbl_clauses size =
  let 
    val l = sbl_clauses_aux2 size 
    fun f (a,b) = if a = ~1 then b else id_pair (a,b)
  in
    map (map_fst f) l
  end
    
(*
val l0 = sbl_clauses 4;
val l1 = sbl_clauses_final 4;
*)    

(* -------------------------------------------------------------------------
   All-in-one initalization
   ------------------------------------------------------------------------- *)

fun init_sat size (blueshape,redshape) =
  let
    val _ = graph_glob := (Array2.array (size,size,0))
    val maxedge = (size * (size - 1)) div 2
    val assignv = Vector.tabulate (maxedge, (fn _ => (ref [], ref [])))
    val clausevv = Vector.fromList []
    val clausel = all_clauses size (blueshape,redshape) @
                  (if !sbl_flag then sbl_clauses size else [])
    val (newassignv,newclausevv) = add_clausel clausel (assignv,clausevv)
  in
    transform_pb (newassignv,newclausevv)
  end

(* -------------------------------------------------------------------------
   Unit propagation
   ------------------------------------------------------------------------- *)

exception Conflict;
  
(* if edgeid < !edgel_n then *)
(* 
else
let fun back () = assignref := 0 in
  assignref := color;
  undol := back :: !undol
end  
*)

fun assign undol edgeid assignref color =
  let
    val graph = !graph_glob
    val (a,b) = project edgeid
    fun back () =
      (
      assignref := 0;
      mat_update (graph,a,b,0); 
      mat_update (graph,b,a,0)
      )
  in
    assignref := color;
    mat_update (graph,a,b,color); 
    mat_update (graph,b,a,color);
    undol := back :: !undol
  end


fun next_free_lit assignv clausev starti =
  if starti >= Vector.length clausev then ~1 else
  let 
    val (edgeid,acolor) = Vector.sub (clausev,starti) 
    val color = !(fst (Vector.sub (assignv,edgeid)))  
  in
    if color = 0 then starti 
    else if color <> acolor then ~2 
    else next_free_lit assignv clausev (starti + 1)
  end
  
fun prop_sat_loop assignv clausevv queue undol = case !queue of 
    [] => (!undol, false)
  | (edgeid, edgecolor) :: _ =>
  let
    val _ = queue := tl (!queue)    
    val (_, (blue_clauses, red_clauses)) = Vector.sub (assignv,edgeid)
      handle Subscript => raise ERR "assignv" (ets (edgeid,edgecolor))
    val clauses_prop = 
      if edgecolor = blue then !blue_clauses else !red_clauses             
    fun f_prop (clauseid,litid) =
      let
        (* fun msg () = its clauseid ^ " " ^ its litid 
           val _ = debugf "clause: " msg () *)
        val (clausev: (int * int) vector,(xref,yref)) = 
          Vector.sub (clausevv,clauseid)
          handle Subscript => raise ERR "clausevv" (its clauseid)
        val otherlitid = if !xref = litid then !yref else !xref
        val (otheredgeid,otherecol) = Vector.sub (clausev,otherlitid)
        val othercol = ! (fst (Vector.sub (assignv,otheredgeid)))
      in
      if othercol = 3 - otherecol 
        then debug "satisfied by other watched literal" 
        else  
      let
        val liti = next_free_lit assignv clausev (Int.max (!xref,!yref) + 1)
        (* val _ = debug ("move: " ^ its litid ^ " to " ^ its liti) *)
      in
        if liti >= 0 then  
        let 
          val (edgei,edgeecol) = Vector.sub (clausev,liti) 
          val (oblue_clauses, ored_clauses) =
            snd (Vector.sub (assignv,edgei))
          val clauses = 
            if edgeecol = blue 
            then oblue_clauses else ored_clauses
          val wref = if !xref = litid then xref else yref    
          fun back () = (wref := litid; clauses := tl (!clauses))      
        in
          undol := back :: !undol;
          wref := liti;
          clauses := (clauseid,liti) :: !clauses
        end
        else if liti = ~2 then () else
        let    
          val (newedgeid,ecolor) = Vector.sub (clausev,otherlitid)
          val propcolor = 3 - ecolor
          val assigncolor = fst (Vector.sub (assignv, newedgeid))
            handle Subscript => 
            raise ERR "assignv" (ets (newedgeid,propcolor))    
        in
          if !assigncolor = propcolor then debug "consistent"
          else if !assigncolor = ecolor then raise Conflict 
          else 
            let 
              fun msg () = ets (newedgeid, propcolor)
              val _ = debugf "prop: " msg ()
              val _ = incr prop_small_counter
            in 
              assign undol newedgeid assigncolor propcolor;
              queue := (newedgeid,propcolor) :: !queue
            end
        end
      end end   
  in
    case ((app f_prop clauses_prop; NONE) 
      handle Conflict => SOME (!undol,true))
    of
      NONE => (* debug "prop loop"; *) 
        prop_sat_loop assignv clausevv queue undol
    | SOME s => s
  end
  

fun prop_sat assignv clausevv (edgeid,color) =
  let 
    val undol = ref []
    val assignref = fst (Vector.sub (assignv,edgeid))
      handle Subscript => raise ERR "assignv" (ets (edgeid,color))
    val queue = ref [(edgeid,color)]
  in
    assign undol edgeid assignref color;
    prop_sat_loop assignv clausevv queue undol
  end

(* -------------------------------------------------------------------------
   Decision
   ------------------------------------------------------------------------- *)

fun rotate n l = 
  let val (l1,l2) = part_n n l in l2 @ l1 end

fun next_assign_aux assignv edgel = case edgel of 
    [] => NONE
  | (i,j) :: m => 
    let val edgeid = id_pair (i,j) in
      if !(fst (Vector.sub (assignv,edgeid))) = 0 
      then SOME edgeid
      else next_assign_aux assignv m
    end
    
fun next_assign f assignv = 
  let 
    (* update array on which f is operating *)
    val n = f ()
    val maxn = length (!edgel_glob)
    val edgel = if n > 0 
      then rotate ((n-1) mod maxn) (!edgel_glob)
      else rotate ((Int.abs n) mod maxn) (!edgel_glob)
    val colorl = if n > 0 then [blue,red] else [red,blue]
  in
    (next_assign_aux assignv edgel,colorl)
  end


(* -------------------------------------------------------------------------
   Degree test
   ------------------------------------------------------------------------- *)

(* degree *)
fun degree_geq n color graph x = 
  length (neighbor_of color graph x) >= n

(* fun test_degree (edgeid,color) =
  let
    val _ = incr degree_counter
    val graph  = !graph_glob
    val degree_limit = if color = red then 13 else 5
    val (a,b) = project edgeid
    val reda = neighbor_of red graph a 
    val redb = neighbor_of red graph b 
    fun test (x,y) = length (commonneighbor_of red graph (x,y)) >= 9
  in
    degree_geq degree_limit color graph a orelse 
    degree_geq degree_limit color graph b orelse
    (if
    (color = red andalso 
     (test (a,b) orelse 
      exists (fn x => test (a,x)) reda orelse
      exists (fn x => test (b,x)) redb)
    )
    then (incr other_counter; true)
    else false)
  end
*)

fun test_degree (edgeid,color) =
  let
    val _ = incr degree_counter
    val graph  = !graph_glob
    val degree_limit = 
      if color = red then !max_red_degree else !max_blue_degree
    val (a,b) = project edgeid
  in
    degree_geq degree_limit color graph a orelse 
    degree_geq degree_limit color graph b
  end


(* -------------------------------------------------------------------------
   Sat solver
   ------------------------------------------------------------------------- *)


exception SatTimeout;
val choose_global = ref (fn () => 0)

fun sat_solver_loop assignv clausevv path = 
  case path of 
    [] => (if !sat_flag then log "sat" else log "unsat"; 
           stats (); not (!sat_flag))
  | (undol,_,[]) :: parentl => 
    (
    debug "undo"; 
    app (fn f => f ()) undol;
    sat_solver_loop assignv clausevv parentl
    )
  | (undol, eido, color :: colorm) :: parentl =>    
  (
  case eido of
    NONE => 
      if !continue_flag 
      then (sat_flag := true;
            incr sat_n; 
       (* graphl := zip_full (normalize_nauty (!graph_glob)) :: !graphl; *)
       (* conel := map (fn (a,b) => 
          mat_sub (!graph_glob,a,b)) (!edgel_glob) :: !conel; *)
       log (string_of_bluegraph (!graph_glob));
       sat_solver_loop assignv clausevv ((undol,eido,[]) :: parentl))
      else
      (log "sat"; 
        log (string_of_bluegraph (!graph_glob)); stats ();
        false)
  | SOME eid =>
     let val _ = debugf "split: " ets (eid,color) in
     if !degree_flag andalso total_time degree_timer test_degree (eid,color)
     then (debug "degree"; 
           incr degree_conflict_counter;
           sat_solver_loop assignv clausevv ((undol,eido,colorm) :: parentl)) 
     else
     let 
       val _ = incr prop_counter
       val _ = if abstract_time > 0 andalso 
          !prop_counter + !prop_small_counter > abstract_time
               then raise SatTimeout else ()
       val (newundol,conflict) = 
         total_time prop_timer (prop_sat assignv clausevv) (eid,color)
         handle Subscript => raise ERR "prop_sat" "subscript"
     in
       if conflict then 
          (
          debug "conflict";
          incr prop_conflict_counter;
          app (fn f => f ()) newundol;
          sat_solver_loop assignv clausevv ((undol,eido,colorm) :: parentl)
          )
       else if !iso_flag andalso is_iso (!graph_glob) then
          (
          debug "iso";
          app (fn f => f ()) newundol;
          sat_solver_loop assignv clausevv ((undol,eido,colorm) :: parentl)
          )   
       else 
         let val (neweido,newcolorl) = next_assign (!choose_global) assignv in
            sat_solver_loop assignv clausevv
               ((newundol, neweido, newcolorl) :: 
                (undol,eido,colorm) :: parentl) 
         end
     end end
  )
  
fun sat_solver size (blueshape,redshape) =
  let
    val _ = init_timer ()
    val _ = isod_glob := eempty IntInf.compare
    val _ = edgel_glob := search_order_linear_undirected size
    val _ = sat_flag := false
    val _ = undirected_flag := true
    val (assignv,clausevv) = init_sat size (blueshape,redshape)
    val (eido,colorl) = next_assign (!choose_global) assignv
    val path = [([],eido,colorl)]
    val _ = log ("variables: " ^ its (Vector.length assignv))
    val _ = log ("clauses: " ^ its (Vector.length clausevv))
  in
    sat_solver_loop assignv clausevv path
  end
  
fun sat_solver_rl f =
  let 
    val _ = choose_global := f 9 (9 * 4) 
    val r = sat_solver 9 (matK 3, matK 4) 
  in
    if r <> true then raise ERR "unsat" "" 
    else SOME (!prop_counter + !prop_small_counter)
  end
  handle SatTimeout => NONE
  
fun ramsey_score p =
  let
    val _ = disable_log := true
    val _ = timeincr := 10000
    val exec = exec_intl.mk_exec p
    fun f a b () = 
      (kernel.init_timer ();
       IntInf.toInt (hd (exec ([IntInf.fromInt a], [IntInf.fromInt b]))))  
    fun g a b () = catch_perror (f a b) () (fn () => raise SatTimeout)
    val r = sat_solver_rl g
  in   
    disable_log := false;
    r
  end
  
(* -------------------------------------------------------------------------
   R(4,5) cone creation
   ------------------------------------------------------------------------- *)  
 
fun starting_graph edgecl (assignv,clausevv) = case edgecl of
    [] => ()
  | ((i,j),c) :: m => 
    let 
      val eid = id_pair (i,j)
      val propc = !(fst (Vector.sub (assignv,eid)))
    in
      if propc = c then starting_graph m (assignv,clausevv) else
      if propc = 0 then
        let val (_,conflict) = prop_sat assignv clausevv (eid,c)
          
          handle Subscript => raise ERR "prop_sat" "subscript"
        in
          if conflict then raise ERR "starting_shape" "conflict1" else
          starting_graph m (assignv,clausevv)
        end  
      else raise ERR "starting_shape" "conflict2"
    end
  
fun create_cone (blueshape,redshape) size sgraph =
  let
    val edgecl = unzip_full_edgecl size (valOf (IntInf.fromString sgraph))
    val _ = log ("edgecl: " ^ string_of_edgecl edgecl)
    val _ = init_timer ()
    val _ = isod_glob := eempty IntInf.compare
    val _ = edgel_glob := List.tabulate (size, fn x => (x,size))
    val _ = sat_flag := false
    val _ = undirected_flag := true
    val (assignv,clausevv) = init_sat (size+1) (blueshape,redshape)
    val _ = log "init_sat"
    val _ = starting_graph edgecl (assignv,clausevv)
    val _ = log ("starting_graph " ^ sgraph ^ ": " ^ 
                  string_of_bluegraph (!graph_glob))
    val (eido,colorl) = next_assign (!choose_global) assignv
    val path = [([],eido,colorl)]
    val _ = log ("variables: " ^ its (Vector.length assignv))
    val _ = log ("clauses: " ^ its (Vector.length clausevv))
  in
    sat_solver_loop assignv clausevv path
  end  
  
(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 20;

val size = 10;
val sl = readl "ramsey_3_5/10";
val sgraph = random_elem sl;

degree_flag := false;
continue_flag := true;
(* max_blue_degree := 4;
   max_red_degree := 8; *)
iso_flag := false; 
disable_log := false;
val (r,t) = add_time (create_cone (matK 4,matK 5) 10) sgraph;


val size = 17;
val sl = readl ("ramsey_4_4/" ^ its size);
val sgraph = random_elem sl;

degree_flag := false;
continue_flag := true;
(* max_blue_degree := 4;
   max_red_degree := 8; *)
iso_flag := false; 
disable_log := false;
val (r,t) = add_time (create_cone (matK 4,matK 5) size) sgraph;

val edgel = List.tabulate (17, fn x => (x,17));



val edgecl = combine (edgel, hd (!conel));
val s0pos = ((~1,0),2);
val s0neg = ((~1,0),1);
val clause = s0pos :: edgecl;
val clausel =  map (fn (x,c) => [s0neg,(x, 3 -c)]) edgecl;

val edgel2 = List.tabulate (17, fn x => (x,17));
 
val edgecl = combine (edgel2, hd (!conel));
val s1pos = ((~1,1),2);
val s1neg = ((~1,1),1);
val clause = s1pos :: edgecl;
val clausel =  map (fn (x,c) => [s1neg,(x, 3 -c)]) edgecl;

fun loop (a,b) k = 
  let 
    val dir = "ramsey_" ^ its a ^ "_" ^ its b ^ "_cones"
    val file = dir ^ "/" ^ k
    
    val _ = mkDir_err dir
    val (r,t) = add_time (create_cone (matK 3,matK 5) 10 sgraph)
  in
    print_endline (its (length (!graphl)));
    writel file (map IntInf.toString (!graphl));
    if r then () else loop (a,b) (k+1)
  end;

*)

(* -------------------------------------------------------------------------
   R(4,5) search loop
   ------------------------------------------------------------------------- *)
 
val satdir_glob = ref selfdir
val subgraphs_glob = ref []
 
fun read_case (a,b) =
  let 
    val file1 = selfdir ^ "/ramsey_3_5/" ^ its a  
    val file2 = selfdir ^ "/ramsey_4_4/" ^ its b
  in
    (Vector.fromList (readl file1), Vector.fromList (readl file2))
  end 
  
fun write_satpb file (nvar,pb) = 
  let 
    val header = "p cnf " ^ its nvar ^ " " ^ its (length pb) 
    fun g (x,c) = if c = 1 then "-" ^ (its (x+1)) else its (x+1)
    fun f clause = String.concatWith " " (map g clause) ^ " 0"
  in
    writel file (header :: map f pb)
  end  
  
(* ,(10,14),(12,12),(13,11) *)
  
fun import_subgraphs () =
  let 
    val cases = [(7,17),(8,16),(9,15)]
    val l0 = map_assoc read_case cases;
    fun f (_,(a,b)) = (Vector.length a, Vector.length b)
    val l1 = map_assoc f l0
  in
    l1
  end
  
  
(*
load "ramsey"; open aiLib kernel ramsey;


val r357 = 
  map (valOf o IntInf.fromString) 
  (readl (selfdir ^ "/ramsey_3_5/7"));
val r357sorted = dict_sort IntInf.compare r357;

val r356 = 
  map (valOf o IntInf.fromString) 
  (readl (selfdir ^ "/ramsey_3_5/6"));
val r356sorted = dict_sort IntInf.compare r356;



val l = map (all_subgraphs 7) r357sorted; 
val lsorted = mk_fast_set IntInf.compare (List.concat l);


(* true is unsat, false is sat or timeout
   prevd is a dictionary of solved pairs for the previous size 
   (empty initially)
   *)

 *)

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

val infts = IntInf.toString
val stinf = valOf o IntInf.fromString

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
                 all_stars edgecd (12,15) csize dsize
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

fun read35 csize = map stinf
  (readl (selfdir ^ "/ramsey_3_5/" ^ its csize))
fun read44 dsize = map stinf
  (readl (selfdir ^ "/ramsey_4_4/" ^ its dsize))



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
    val subexpdir = expdir ^ "_" ^ 
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

val expdir = selfdir ^ "/exp/r45_4";
clean_dir expdir;
eval_loop35 expdir (10,10) 14;



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

