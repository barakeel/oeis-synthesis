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


val undirected_flag = ref false

(* flags conspiring to output all models *)
val continue_flag = ref false
val sat_flag = ref false
val degree_flag = ref false

(* -------------------------------------------------------------------------
   Logging
   ------------------------------------------------------------------------- *)

val disable_log = ref false
fun log s = if !disable_log then () else print_endline s 

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
  
  
  if !norm_failure > 0 then log ("norm: " ^ its (!norm_failure)) else ()
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
    val _ = debugf "graph: " string_of_graph graph
    val normgraph = normalize_nauty graph
    val _ = debugf "normgraph: " string_of_graph normgraph
    val graphid = zip_mat normgraph
    val _ = debugf "graphid: " IntInf.toString graphid
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
   Unit propagation
   ------------------------------------------------------------------------- *)

val convertv = Vector.fromList (search_order_undirected 50);
fun project x = Vector.sub (convertv,x);
fun id_pair (x,y) = x + ((y * (y - 1)) div 2);

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
  let fun f (bref,lit) = bts (!bref) ^ "@" ^ ets (fst (fst lit), snd lit) in
    String.concatWith " " (map f (vector_to_list clausev))
  end
  
fun string_of_assignv assignv = 
  let 
    val l1 = map (! o fst) (vector_to_list assignv)
    val l2 = number_fst 0 l1
  in
    String.concatWith " " (map ets l2)
  end  

(* inefficient *)
val graph_glob = ref (Array2.array (1,1,0));
val isograph_glob = ref (Array2.array (1,1,0));

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
        val vcid = length (!l) + 1
      in
        l := (cid,cvid) :: !l; (* link from var to clauses *)
        ((vid,vcid),color)
      end
    val newclausev = Vector.fromList (mapi f clause)
    val newclausevv = Vector.concat [clausevv,Vector.fromList [newclausev]]
  in
    (newassignv, newclausevv)
  end
  
fun add_clausel clausel (assignv,clausevv) = 
  foldl add_clause (assignv,clausevv) clausel
  

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

fun extra_clauses size = 
  let 
    val ltop = tl (map (fn i => (0,i)) (List.tabulate (size,I))) 
    fun loop l = case l of [] => [] | [a] => []
      | a :: b :: m => [(id_pair a,red),(id_pair b,blue)] :: loop (b :: m)  
  in
    loop ltop
  end


fun transform_pb (assignv,clausevv) = 
  let 
    fun f1 (l1,l2) = (ref 0, 
      (dlv_fromlist (~1,~1) (rev (!l1)), dlv_fromlist (~1,~1) (rev (!l2))))
    fun f2 x = (Vector.map (fn y => (ref false, y)) x, ref 0)
  in
    (Vector.map f1 assignv, Vector.map f2 clausevv)
  end

fun init_sat size (blueshape,redshape) =
  let
    val _ = graph_glob := (Array2.array (size,size,0))
    val maxedge = (size * (size - 1)) div 2
    val assignv = Vector.tabulate (maxedge, (fn _ => (ref [], ref [])))
    val clausevv = Vector.fromList []
    val clausel = all_clauses size (blueshape,redshape) (* @ 
                  extra_clauses size *)
    val (newassignv,newclausevv) = add_clausel clausel (assignv,clausevv)
  in
    transform_pb (newassignv,newclausevv)
  end

exception Conflict;

fun propagated_clause clausev = 
  let fun loop i = 
    let val (bref,lit) = Vector.sub (clausev,i) in
      if not (!bref) then lit else loop (i+1)
    end
  in
    loop 0
  end
  handle Subscript => 
    raise ERR "propagated_clause" (string_of_clausev clausev)


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
  

fun prop_sat_loop assignv clausevv queue undol = case !queue of 
    [] => (!undol, false)
  | (edgeid, edgecolor) :: _ =>
  let
    val _ = queue := tl (!queue)    
    val (_, (blue_clauses, red_clauses)) = Vector.sub (assignv,edgeid)
    val (clauses_prop,clauses_del) = 
      if edgecolor = blue then (blue_clauses, red_clauses) 
                          else (red_clauses, blue_clauses)
    fun f_prop (clauseid,litid) = 
      let
        fun msg () = its clauseid ^ " " ^ its litid
        (* val _ = debugf "clause: " msg () *)
        val (clausev,nref) = Vector.sub (clausevv,clauseid)
        val (bref,_) = Vector.sub (clausev,litid)
        val _ = if !bref
                then raise ERR "propagate_sat" "bref not reset"
                else ()
        val _ = (bref := true; incr nref)
        val _ = undol := (fn () => (bref := false; decr nref)) :: !undol
      in
        (* happens if a clause contains only one literal *)
        (* find a better way to exit that raising an exception *)
        if !nref > Vector.length clausev - 1 then raise Conflict else
        if !nref < Vector.length clausev - 1 then () else
        let 
          (* val _ = debug "propagated" *)
          val ((newedgeid,_),tempcolor) = propagated_clause clausev
          val propcolor = 3 - tempcolor
          val assigncolor = fst (Vector.sub (assignv, newedgeid))
            handle Subscript => raise ERR "assignv" (ets (newedgeid,propcolor))
        in
          if !assigncolor = propcolor then () 
          else if !assigncolor = tempcolor then raise Conflict 
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
      end
    (* delete links of all unassigned literals *)  
    fun f_del (clauseid, litid) =   
      let 
        (* val _ = debug "delete" *)
        val (clausev,nref) = Vector.sub (clausevv,clauseid)
        fun f (bref,((edgeid,ecid),color)) = if !bref then () else
          let 
            val bothdlv = snd (Vector.sub (assignv,edgeid))
            val dlv = if color = blue then fst bothdlv else snd bothdlv
            val undof = dlv_del ecid dlv
              handle Subscript => raise ERR "dlv_del" 
                (ets (edgeid,color) ^ "~" ^ its ecid)
          in 
            undol := undof :: !undol
          end
      in
        Vector.app f clausev
      end      
  in
    case 
      ((dlv_app f_prop clauses_prop; 
        dlv_app f_del clauses_del;
       NONE) 
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
    val queue = ref [(edgeid,color)]
  in
    assign undol edgeid assignref color;
    prop_sat_loop assignv clausevv queue undol
  end

(* next decision variable *)

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
    val maxn = Vector.length assignv
    val edgel = if n > 0 
      then rotate ((n-1) mod maxn) (!edgel_glob)
      else rotate ((Int.abs n) mod maxn) (!edgel_glob)
    val colorl = if n > 0 then [blue,red] else [red,blue]
  in
    (next_assign_aux assignv edgel,colorl)
  end



(* degree *)
fun degree_geq n color graph x = 
  length (neighbor_of color graph x) >= n

fun test_degree (edgeid,color) =
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
            log (string_of_bluegraph (!graph_glob));
            sat_solver_loop assignv clausevv ((undol,eido,[]) :: parentl))
      else
      (log "sat"; stats ();
        log (string_of_bluegraph (!graph_glob));
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
       else if is_iso (!graph_glob) then
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
    val _ = exec_intl.edgev_glob := assignv
    val _ = if length (!edgel_glob) <> Vector.length assignv
            then raise ERR "sat_solver" "variables"
            else ()
    val (eido,colorl) = next_assign (!choose_global) assignv
    val path = [([],eido,colorl)]
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
  
end (* struct *)

(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;
degree_flag := true;
continue_flag := true;
val (r,t) = add_time (sat_solver 17) (matK 3,matK 6);
debug_flag := true;
val (r,t) = add_time (sat_solver 5) (matK 3,matK 3);
debug_flag := false;
val (r,t) = add_time (sat_solver 14) (matK 4,matK 4);

val (r,t) = add_time (sat_solver 22) (matK 4,matK 5);

fun f (a:int) (b:unit) = random_int (~100,100);
*)

(*
PolyML.print_depth 0;
load "ramsey"; load "game"; open aiLib kernel ramsey;
PolyML.print_depth 10;
val p = game.random_prog 10;
val p = Ins(0,[]);
human.humanf p;
val sc = ramsey_score p;
*)

