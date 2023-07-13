(* convention: false means continue and true means stop *)
   
structure ramsey :> ramsey =
struct   

open HolKernel Abbrev boolLib aiLib kernel smlParallel
val ERR = mk_HOL_ERR "ramsey"


(* -------------------------------------------------------------------------
   Parameters (edit the file to make the changes)
   ------------------------------------------------------------------------- *)

val limit_glob = ref (NONE, SOME 10.0)
val parallel_flag = ref true

(* -------------------------------------------------------------------------
   Logging
   ------------------------------------------------------------------------- *)

val log_file = ref (selfdir ^ "/ramsey_log")
val parallel_flag = ref true
local fun log s = append_endline (!log_file) s
in
  fun logp s = if !parallel_flag 
               then print_endline s
               else (print_endline s; log s)
end


(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val blue = 1
val red = 2
val blue_array_glob = ref (Array.fromList [true])
val red_array_glob = ref (Array.fromList [true])
val blue_prop_glob = ref (Array.fromList [[(0,0)]])
val red_prop_glob = ref (Array.fromList [[(0,0)]])
val edgel_glob = ref [(0,0)]
val blue_size_glob = ref 0
val red_size_glob = ref 0
val counter = ref 0
val limit_glob = ref (SOME 10000, NONE)
val time_glob = ref (SOME (Time.fromReal 0.0))
val timer = ref (Timer.startRealTimer ())
val isod_glob = ref (eempty IntInf.compare)

(* -------------------------------------------------------------------------
   Timer
   ------------------------------------------------------------------------- *)

exception RamseyTimeout;

fun init_timer () =
  (
  counter := 0;
  time_glob := Option.map Time.fromReal (snd (!limit_glob));
  timer := Timer.startRealTimer ()
  )

fun test_timer () =
  let
    val _ = incr counter
    val _ = if !counter mod 1000 = 0 then print "." else ()
    val _ = case fst (!limit_glob) of
        NONE => ()
      | SOME ti => 
        if !counter > ti then raise RamseyTimeout else ()
    val _ = case !time_glob of
        NONE => ()
      | SOME tr => 
        if Timer.checkRealTimer (!timer) > tr then raise RamseyTimeout else ()
  in
    ()
  end

(* -------------------------------------------------------------------------
   Adjacency matrix representation
   ------------------------------------------------------------------------- *)

type mat = int Array2.array
fun mat_sub (m,i,j) = Array2.sub (m,i,j)
fun mat_update (m,i,j,v) = Array2.update (m,i,j,v)
fun mat_update_sym (m,i,j,v) =
  (mat_update (m,i,j,v); mat_update (m,j,i,v));

fun mat_tabulate (n,f) = Array2.tabulate Array2.RowMajor (n,n,f)
fun mat_appi f m = 
  let val range = {base=m,row=0,col=0,nrows=NONE,ncols=NONE} in
    Array2.appi Array2.RowMajor f range
  end

local open IntInf in
  fun zip_mat m =
    let val r = ref 1 in
      mat_appi (fn (i,j,x) => if i = j then () else r := !r * 3 + 
        IntInf.fromInt x) m; !r
    end
end

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
fun symmetrify size m = 
  mat_tabulate (size, fn (a,b) => 
  if a=b then 0 else if a < b then mat_sub (m,a,b) else mat_sub (m,b,a));
fun random_symmat size = symmetrify size (random_mat size);
 
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
    mat_tabulate (newgraphsize, fn (i,j) => 
      if (i,j) = edge then color 
      else if i >= graphsize orelse j >= graphsize then 0
      else mat_sub (graph,i,j))
  end
  
fun mat_addl edgecl graph = foldl (uncurry mat_add) graph edgecl

(* assumes mat contains 1 and 0s *)    
fun mat_to_int_fixedsize m = 
  let val r = ref 0 (* can start at zero because all the same size *) in
    mat_appi (fn (i,j,x) => if i = j then () else r := !r * 2 + x) m; !r
  end;  
    
fun mat_to_int m = 
  let val r = ref 1 in
    mat_appi (fn (i,j,x) => if i = j then () else r := !r * 2 + x) m; !r
  end;

fun neighbor_of color graph x = 
  let 
    val vertexl = List.tabulate (mat_size graph,I)
    fun test y = mat_sub (graph,x,y) = color
  in
    (x, filter test vertexl)
  end
  
fun all_neighbor color graph = 
  List.tabulate (mat_size graph, neighbor_of color graph) 

fun string_of_edgecl edgecl = 
  let fun f ((i,j),x) = its i ^ "," ^ its j ^ ":" ^ its x in
    String.concatWith " " (map f edgecl)
  end
  
fun string_of_graph graph = 
  let fun f (i,l) = its i ^ " -> " ^ String.concatWith " " (map its l) in
    String.concatWith ", " (map f (all_neighbor blue graph)) ^ " | " ^
    String.concatWith ", " (map f (all_neighbor red graph))
  end
  
fun string_of_bluegraph graph = 
  let fun f (i,l) = its i ^ " -> " ^ String.concatWith " " (map its l) in
    String.concatWith ", " (map f (all_neighbor blue graph))
  end
  
fun string_of_redgraph graph = 
  let fun f (i,l) = its i ^ " -> " ^ String.concatWith " " (map its l) in
    String.concatWith ", " (map f (all_neighbor red graph))
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
   Shapes: computes all isomorphism of an input shape before starting
   ------------------------------------------------------------------------- *)

(* todo: optimize for undirected graphs *)
fun isomorphic_shapes shape =
  let
    val shapesize = Int.min (Array2.dimensions shape)
    val perml = permutations (List.tabulate (shapesize,I))
    val permfl = map mk_permf perml
    val shapel = map (mat_permute (shape,shapesize)) permfl
    val shaped = enew (mat_compare_fixedsize shapesize) shapel
    val _ = print_endline (its (elength shaped) ^ " isomorphic variants")
  in
    (elist shaped, shapesize)
  end;
  
fun normalize_naively mat =
  let 
    val size = mat_size mat 
    val fl = map mk_permf (permutations (List.tabulate (size,I)))  
    val matl = map (mat_permute (mat,size)) fl
  in
    hd (dict_sort (mat_compare_fixedsize size) matl)
  end


fun neighbor_of_color color size m x = 
  let fun test y = mat_sub (m,x,y) = color in
    filter test (List.tabulate (size,I))
  end
  
fun all_neighbor_color color size m = 
  List.tabulate (size, neighbor_of_color color size m)
  
fun normalize_weak m =
  let 
    val size = mat_size m
    val blueneighl = map length (all_neighbor_color blue size m)
    val redneighl = map length (all_neighbor_color red size m)
    val neighl = number_fst 0 (combine (blueneighl,redneighl))
    val cmp = snd_compare (cpl_compare Int.compare Int.compare)
    val neighsortedl = dict_sort cmp neighl
    val permutation = map fst neighsortedl
    val sigma = mk_permf permutation
  in
    mat_permute (m,size) sigma
  end
  
(* -------------------------------------------------------------------------
   Test if a shape is a subgraph of a bigger graph
   ------------------------------------------------------------------------- *)
   
fun subsets_of_size n l = case l of
    [] => if n = 0 then [[]] else []
  | a :: m => 
    let
      val l1 = map (fn subset => a::subset) (subsets_of_size (n - 1) m)
      val l2 = subsets_of_size n m
    in
      l1 @ l2
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
  
fun has_shape_wcedge (i,j) graph color =
  let 
    val shapesize = if color = blue then !blue_size_glob else !red_size_glob
    val barray = if color = blue then !blue_array_glob else !red_array_glob
    val unigraph = keep_only color graph
    val vertexl = List.tabulate (mat_size unigraph, I)
    val l0 = filter (fn x => not (mem x [i,j])) vertexl
    val l1 = subsets_of_size_faster (shapesize-2) (l0,length l0)
    fun f subset =
      let 
        val sigma = mk_permf (i :: j :: subset)
        val candshape = mat_permute (unigraph,shapesize) sigma
      in
        Array.sub (barray, mat_to_int_fixedsize candshape)
      end
  in
    exists f l1
  end;   

fun has_shape_wedge edge graph =
  has_shape_wcedge edge graph blue orelse
  has_shape_wcedge edge graph red
  
  
fun has_shape_c graph color =
  let 
    val shapesize = if color = blue then !blue_size_glob else !red_size_glob
    val barray = if color = blue then !blue_array_glob else !red_array_glob
    val unigraph = keep_only color graph
    val vertexl = List.tabulate (mat_size unigraph, I)
    val l1 = subsets_of_size_faster shapesize (vertexl,mat_size unigraph)
    fun f subset =
      let 
        val sigma = mk_permf subset
        val candshape = mat_permute (unigraph,shapesize) sigma
      in
        Array.sub (barray, mat_to_int_fixedsize candshape)
      end
  in
    exists f l1
  end;   

fun has_shape graph =
  has_shape_c graph blue orelse
  has_shape_c graph red  
  
(* -------------------------------------------------------------------------
   Test isomorphism
   ------------------------------------------------------------------------- *)
    
fun is_iso graph =     
  let val graphid = zip_mat (normalize_weak graph) in
    if emem graphid (!isod_glob)   
    then true
    else (isod_glob := eadd graphid (!isod_glob); false)
  end
  
fun check_iso grapho = case grapho of 
    NONE => NONE 
  | SOME graph => if is_iso graph then NONE else SOME graph

(* -------------------------------------------------------------------------
   Unit propagation
   ------------------------------------------------------------------------- *)
  
fun propagate_color graphtop color =
  let 
    val r = ref (eempty (cpl_compare Int.compare Int.compare))
    val shapesize = if color = blue 
      then !blue_size_glob else !red_size_glob    
    val graphsize = mat_size graphtop
    val graph = keep_only color graphtop    
    val subsetl = subsets_of_size_faster shapesize
      (List.tabulate (graphsize,I),graphsize)
    val prop_glob = if color = blue 
      then !blue_prop_glob else !red_prop_glob
    fun loop subsetl = case subsetl of [] => NONE | subset :: subsetcont =>
      let 
        val sigma = mk_permf subset
        val candshape = mat_permute (graph,shapesize) sigma
        val candedgel = Array.sub (prop_glob, mat_to_int_fixedsize candshape)
        fun subloop l = case l of 
            [] => loop subsetcont
          | (i,j) :: edgecont => 
            (r := eadd (sigma i, sigma j) (!r); subloop edgecont)
      in
        subloop candedgel
      end 
  in
    loop subsetl; !r
  end

fun propagate_one graph = 
  let
    val _ = debugf "prop: " string_of_graph graph
    val _ = test_timer ()
    val rededged = propagate_color graph blue
    val rededgel = map_assoc (fn _ => red) (elist rededged)
    val blueedged = propagate_color graph red
    val blueedgel = map_assoc (fn _ => blue) (elist blueedged)
    val graphedgecl = mat_to_edgecl graph
    val _ = if null blueedgel 
            then ()
            else debugf  "prop blue: " string_of_edgecl blueedgel
    val _ = if null rededgel 
            then () 
            else debugf  "prop red: " string_of_edgecl rededgel
  in
    case edge_conflict (rededgel @ blueedgel @ graphedgecl) of
      NONE => (debug "prop conflict"; NONE)
    | SOME edgecl => 
      let val newedgecl = filter (fn ((i,j),_) => 
        mat_sub (graph,i,j) = 0) edgecl
      in
        if null newedgecl
        then SOME (true, graph)
        else (debugf  "prop update: " string_of_edgecl newedgecl; 
              SOME (false, mat_addl newedgecl graph))
      end
  end
   
fun propagate_loop graph = case propagate_one graph of
    NONE => NONE
  | SOME (true,newgraph) => SOME newgraph
  | SOME (false,newgraph) => propagate_loop newgraph

fun propagate graph = propagate_loop graph

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

fun pairbelowy y = List.tabulate (y+1,fn x => (x,y));

fun search_order size =
  let 
    val search_order0 = List.concat (List.tabulate (size,fn y => pairbelowy y))
    val search_order1 = filter (fn (x,y) => x <> y) search_order0
    val search_order2 = 
      List.concat (map (fn (x,y) => [(x,y),(y,x)]) search_order1)
  in
    search_order2
  end

fun next_edge_aux graphsize graph edgel = case edgel of
    [] => NONE
  | (i,j) :: m => 
    if i >= graphsize orelse j >= graphsize then SOME (i,j) 
    else if mat_sub (graph,i,j) = 0 then SOME (i,j)
    else next_edge_aux graphsize graph m
  
fun next_edge graph = next_edge_aux (mat_size graph) graph (!edgel_glob)      

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

fun add_break () = if !counter >= 1000 then logp "" else () 
fun stats () = logp ("isomorphic graphs: " ^ its (elength (!isod_glob)))
fun search_end grapho = case grapho of 
    NONE => (add_break (); logp "unsat"; 
    stats (); true) 
  | SOME graph => (add_break (); logp "sat"; 
    logp (string_of_graph graph); stats(); false)
    
fun search_loop path = 
  case path of 
    [] => search_end NONE
  | (graph, []) :: parentl => search_loop parentl
  | (graph, color :: colorm) :: parentl =>    
    (
    case next_edge graph of
      NONE => search_end (SOME graph)
    | SOME edge =>
      let 
        fun f () = its (fst edge) ^ "," ^ its (snd edge) ^ ":" ^ its color
        val candgraph = mat_add (edge,color) graph 
      in
        debugf "split: " f ();
        test_timer ();
        if has_shape_wedge edge candgraph
        then (debug "conflict"; search_loop ((graph,colorm) :: parentl))
        else
        (
        case check_iso (propagate candgraph) of
          NONE => search_loop ((graph,colorm) :: parentl)
        | SOME newgraph =>
          let 
            val child = (newgraph,[blue,red])
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
    val _ = edgel_glob := search_order size
    val path = [(mat_tabulate (1, fn (i,j) => 0),[blue,red])]
  in
    search_loop path
  end


(* -------------------------------------------------------------------------
   Graph representations: set of edges, neighbors, adjacency matrices
   ------------------------------------------------------------------------- *)

fun edgecl_to_mat_size size edgecl =
  let 
    val edgel = map fst edgecl
    val edged = dnew (cpl_compare Int.compare Int.compare) edgecl
    fun f (i,j) = case dfindo (i,j) edged of NONE => 0 | SOME c => c 
  in
    mat_tabulate (size, f)
  end  
  
fun mat_to_edge1l m =
  let 
    val r = ref []
    fun f (i,j,x) = if i = j orelse x = 0 then () else 
      r := ((i,j),1) :: !r
  in
    mat_appi f m; !r
  end

fun read_edgel s =
  map pair_of_list
  (mk_batch 2 (map string_to_int (String.tokens (not o Char.isDigit) s)))

fun read_shape file =
  let 
    val sl = readl file
    val reds = List.nth (sl,5)
    val blues = List.nth (sl,6)
  in
    (edgecl_to_mat (map_assoc (fn _ => blue) (read_edgel blues)),
     edgecl_to_mat (map_assoc (fn _ => red) (read_edgel reds)))
  end
  
(* -------------------------------------------------------------------------
   Enumerating all supershapes of multiples shape
   ------------------------------------------------------------------------- *)

fun supershapes_one_aux size edge1l =
  let 
    val edgel1 = search_order size 
    val edgel2 = filter (fn x => not (mem x (map fst edge1l))) edgel1
    val l1 = cartesian_productl (map (fn x => [(x,0),(x,1)]) edgel2)
    val l2 = map (fn x => edge1l @ x) l1
    val il = map (fn x => mat_to_int_fixedsize (edgecl_to_mat_size size x)) l2
  in
    il
  end; 

fun supershapes_one size shape = 
  supershapes_one_aux size (mat_to_edge1l shape)
  
fun supershapes (shapel,size) = 
  let 
    val a = Array.tabulate (int_pow 2 (size * (size - 1)), fn _ => false)
    fun f shape = 
      let val il = supershapes_one size shape in
        app (fn x => Array.update (a,x,true)) il
      end
  in
    app f shapel;
    a
  end 

(* -------------------------------------------------------------------------
   Enumerating all supershapes of subshapes for unit propagation
   ------------------------------------------------------------------------- *)
   

fun all_split l =
  let val l1 =
    map (fn chosen => (filter (fn x => x <> chosen) l, chosen)) l
  in
    map (fn (a,b) => (a,fst b)) l1
  end
  
fun insert_ol cmp x l = case l of
    [] => [x]
  | a :: m => 
    (case cmp (x,a) of
      EQUAL => l 
    | LESS => x :: l
    | GREATER => a :: insert_ol cmp x m
    )

val cmpii = cpl_compare Int.compare Int.compare
fun update_proparray a (il,edge) =
  app (fn x => Array.update (a,x, insert_ol cmpii edge (Array.sub (a,x)))) il

fun propshapes shape = 
  let
    val (isoshapel,size) = isomorphic_shapes shape
    val (a: (int*int) list array) = 
      Array.tabulate (int_pow 2 (size * (size - 1)), fn _ => [])
    val subshapel = List.concat (map (all_split o mat_to_edge1l) isoshapel)
    fun f size (shape,edge) = (supershapes_one_aux size shape, edge)
    val (_,t) = add_time (app (update_proparray a o f size)) subshapel;
  in
    print_endline ("propshapes: " ^ rts_round 2 t);
    a
  end

(* -------------------------------------------------------------------------
   Precompute supershapes of shape in dr100
   ------------------------------------------------------------------------- *)

fun mat_appi f m = 
  let val range = {base=m,row=0,col=0,nrows=NONE,ncols=NONE} in
    Array2.appi Array2.RowMajor f range
  end

fun all_shapes () =
  let 
    val filel = listDir (selfdir ^ "/dr100");
    val cnfl = filter (fn x => String.isSuffix "_cnf.p" x) filel
    val brshapel = map_assoc (read_shape o (fn x => "dr100/" ^ x)) cnfl
    val l1 = map snd brshapel;
    val l2 = map (fn (a,b) => (keep_only blue a, keep_only red b)) l1;
 in 
   List.concat (map (fn (a,b) => [a,b]) l2)
 end

fun normalize_shapes l3 =
  let
    val l4 = map swap (map_assoc mat_to_int l3)
    val d = dregroup Int.compare l4
    val l5 = map (fn (a,b) => (a,hd b)) (dlist d)
    val l6 = map (normalize_naively o snd) l5
    val l7 = map swap (map_assoc mat_to_int l6);
    val d2 = dregroup Int.compare l7 
    val l8 = map (fn (a,b) => (a,hd b)) (dlist d2)  
 in
   l8
 end

fun ats a = String.concatWith " "
  (map (fn x => if x then its 1 else its 0) (array_to_list a));

fun compute_write_supershapes ishapel =
  let 
    fun f (i,shape) = 
      let val a = supershapes (isomorphic_shapes shape) in
        writel (selfdir ^ "/dr100shapes/" ^ its i) [ats a]
      end
  in
    app f ishapel
  end
  
fun propts a = 
  let 
    fun f (x,y) =  its x ^ "," ^ its y
    fun g l = String.concatWith " " (map f l)
  in
    map g (array_to_list a) 
  end
  
fun compute_write_propshapes ishapel =
  let fun f (i,shape) = 
    writel (selfdir ^ "/dr100propshapes/" ^ its i) 
      (propts (propshapes shape))
  in
    app f ishapel
  end 
  
(*  
load "ramsey"; open aiLib kernel ramsey;
val ishapel = normalize_shapes (all_shapes ());
val (_,t) = add_time compute_write_propshapes ishapel;
*) 

(* -------------------------------------------------------------------------
   Experiment
   ------------------------------------------------------------------------- *)
 
fun read_array file = Array.fromList
  (map (fn s => s = "1") (String.tokens Char.isSpace (hd (readl file))))
  
fun read_prop file = 
  let 
    fun read_entry s = 
      let val (a,b) = split_string "," s in 
        (string_to_int a, string_to_int b) 
      end
    fun read_line s = 
      map read_entry (String.tokens Char.isSpace s)
  in
    Array.fromList (map read_line (readl_empty file))
    (* some lines are empty and it is important *)
  end 
 
fun init_shapes (blueshape,redshape) =
  let
    val shapedir = selfdir ^ "/dr100shapes"
    val propdir = selfdir ^ "/dr100propshapes"
    val blueshape_norm = normalize_naively (keep_only blue blueshape)
    val redshape_norm = normalize_naively (keep_only red redshape)
    val bluefile = shapedir ^ "/" ^ its (mat_to_int blueshape_norm)
    val redfile = shapedir ^ "/" ^ its (mat_to_int redshape_norm)
    val bluepropfile = propdir ^ "/" ^ its (mat_to_int blueshape_norm) 
    val redpropfile = propdir ^ "/" ^ its (mat_to_int redshape_norm) 
    val _ =  
       if exists_file bluefile
       then blue_array_glob := read_array bluefile
       else raise ERR "reading blue supershapes" bluefile
    val _ =  
       if exists_file redfile
       then red_array_glob := read_array redfile
       else raise ERR "reading red supershapes" redfile
    val _ =  
       if exists_file bluepropfile
       then blue_prop_glob := read_prop bluepropfile
       else raise ERR "reading blue prop supershapes" bluepropfile
    val _ =  
       if exists_file redpropfile
       then red_prop_glob := read_prop redpropfile
       else raise ERR "reading red prop supershapes" redpropfile
    val _ = blue_size_glob := mat_size blueshape
    val _ = red_size_glob := mat_size redshape
  in
    ()
  end  

fun search_each_size (blueshape,redshape) =
  let
    val _ = print_endline ("blue shape: " ^ string_of_bluegraph blueshape)
    val _ = print_endline ("red shape:  " ^ string_of_redgraph redshape)
    val (_,t) = add_time init_shapes (blueshape,redshape)
    val _ = print_endline ("reading supershapes: " ^ rts_round 2 t)
    val initsize = Int.max (mat_size blueshape, mat_size redshape) 
    fun loop csize =
      let 
        val _ = logp ("search with graph size: " ^ its csize)  
        val b = search csize
        val _ = print_endline ""
      in
        if b then (true,csize) else loop (csize + 1)
      end
      handle RamseyTimeout => 
        (add_break (); logp "timeout"; stats(); (false,csize)) 
  in
    loop initsize 
  end

fun run expname = 
  let
    val expdir = selfdir ^ "/exp/" ^ expname
    val _ = app mkDir_err [selfdir ^ "/exp", expdir]
    val _ = log_file := expdir ^ "/log"
    val filel = ["adr_o3_o3_rb_inf_cnf.p"]
    val filel = listDir (selfdir ^ "/dr100")
    val cnfl = filter (fn x => String.isSuffix "_cnf.p" x) filel
    val brshapel = map_assoc (read_shape o (fn x => "dr100/" ^ x)) cnfl
    fun f ((file,brshape),i) = 
       let 
         val _ = logp ("File " ^ its i ^ ": " ^ file)
         val (r,t) = add_time search_each_size brshape
         val _ = logp ("file time: " ^ rts_round 2 t)
       in
         r
       end 
    val (rl,t) = add_time (map f) (number_snd 0 brshapel)
    val _ = logp ("total time: " ^ rts_round 2 t)
    val l = filter (fst o snd) (combine (cnfl,rl))
    fun g (s,(_,n)) = s ^ ": " ^ its n; 
    val _ = writel (expdir ^ "/results") (map g l)
  in
    rl
  end
  
(* -------------------------------------------------------------------------
   Parallel execution
   ------------------------------------------------------------------------- *)

fun ramseyspec_fun param file =
   let 
     val _ = logp ("File: " ^ file)
     val brshape = (read_shape o (fn x => selfdir ^ "/dr100/" ^ x)) file
     val (r,t) = add_time search_each_size brshape
     val _ = logp ("file time: " ^ rts_round 2 t)
   in
     r
   end 

val ramseyspec : (unit, string, (bool * int)) extspec =
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
  write_arg = let fun f file s = writel file [s] in f end,
  read_arg = let fun f file = hd (readl file) in f end,
  write_result = let fun f file (b,i) = 
     writel file [bts b ^ " " ^ its i] 
     in f end,
  read_result = let fun f file = 
    let val (s1,s2) = split_string " " (hd (readl file)) in 
      (string_to_bool s1, string_to_int s2)
    end
    in f end
  }

fun parallel_ramsey ncore expname filel =
  let  
    val _ = parallel_flag := true
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = mkDir_err dir
    val _ = smlExecScripts.buildheap_dir := dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) 
      handle NotFound => 12000) 
    val (rl,t) = add_time (parmap_queue_extern ncore ramseyspec ()) filel
    val l = filter (fst o snd) (combine (filel,rl))
    fun g (s,(_,n)) = s ^ ": " ^ its n  
  in
    parallel_flag := false;
    writel (dir ^ "/log") ["time: " ^ rts t];
    writel (dir ^ "/results") (map g l);
    l
  end
 
  
end (* struct *) 
  
  
(*
load "ramsey"; open aiLib kernel ramsey;
val filel = listDir (selfdir ^ "/dr100");
val cnfl = filter (fn x => String.isSuffix "_cnf.p" x) filel;
val expname = "aaa_para6";
val rl = parallel_ramsey 4 expname cnfl;
*)

