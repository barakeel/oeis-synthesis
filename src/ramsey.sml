(* again not sure about the matrix representation but it allows fast 
   access to individual edges it's uses a lot of memory and time for nothing
   when udpating *)
   
structure ramsey :> ramsey =
struct   

open HolKernel Abbrev boolLib aiLib kernel smlParallel
val ERR = mk_HOL_ERR "ramsey"

val log_file = ref (selfdir ^ "/ramsey_log")
fun log s = append_endline (!log_file) s
fun logp s = (print_endline s; log s)

val blue_array_glob = ref (Array.fromList [true]);
val red_array_glob = ref (Array.fromList [true]);
val blue_size_glob = ref 0;
val red_size_glob = ref 0;

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

fun mat_copy (m,gsize) =
  let fun f (x,y) = mat_sub (m,x,y) in
    mat_tabulate (gsize, f)
  end
(* warning: sigma should be the inverse permutation *)
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
  
(* assumes mat contains 1 and 0s *)    
fun mat_to_int m = 
  let val r = ref 0 (* can start at zero because all the same size *) in
    mat_appi (fn (i,j,x) => if i = j then () else r := !r * 2 + x) m; !r
  end;  
    
(* -------------------------------------------------------------------------
   Neighbor representation (most compact)
   -------------------------------------------------------------------------
*)
  
(* -------------------------------------------------------------------------
   Edge representation (fastest to udpate, maybe less garbage collection)
   -------------------------------------------------------------------------
*)   

(* maybe tell the list of edges needed to be colored *)

    
    
(* -------------------------------------------------------------------------
   Characteristic function: complexity is vertices cubed
   ------------------------------------------------------------------------- *)

(* warning: assumes symmetry *)
fun neighbor_of size m x = 
  let fun test y = mat_sub (m,x,y) = 1 in
    filter test (List.tabulate (size,I))
  end;
  
fun all_neighbor size m = Vector.tabulate (size, neighbor_of size m);

fun charac_vertex nv x =
  let
    val l = ref []
    fun loop nl = 
      let 
        val nll = map (fn y => Vector.sub (nv,y)) nl
        val newnl = mk_fast_set Int.compare (nl @ List.concat nll) 
      in
        if newnl = nl then () else (l := length newnl :: !l; loop newnl)
      end
  in
    loop [x]; rev (!l)
  end

fun charac size m =
  let val nv = all_neighbor size m in
    List.tabulate (size, fn x => (x,charac_vertex nv x))   
  end;

(* -------------------------------------------------------------------------
   Isomorphic graphs
   ------------------------------------------------------------------------- *)

fun allij size f =
  let fun loop i j =
    if i >= size then true else
    if j >= size then loop (i+1) 0 else
    if f(i,j) then loop (i+1) j else false
  in
    loop 0 0
  end;
  
fun miso size (m1: int Array2.array,sigma1) (m2,sigma2) = 
  allij size (fn (x,y) => 
    mat_sub (m1, sigma1 x, sigma1 y) = mat_sub (m2, sigma2 x, sigma2 y));
 
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
fun array2_compare_aux size a1 a2 i j = 
  case Int.compare (Array2.sub (a1,i,j),Array2.sub (a2,i,j)) of
      EQUAL => if j >= size - 1 then 
                 if i >= size - 1 
                 then EQUAL 
                 else array2_compare_aux size a1 a2 (i+1) 0
               else array2_compare_aux size a1 a2 i (j+1)
    | r => r;
  
fun array2_compare size (a1,a2) = 
  array2_compare_aux size a1 a2 0 0;

fun init_shape shape =
  let
    val shapesize = Int.min (Array2.dimensions shape)
    val perml = permutations (List.tabulate (shapesize,I))
    val permfl = map mk_permf perml
    val shapel = map (mat_permute (shape,shapesize)) permfl
    val shaped = enew (array2_compare shapesize) shapel
    val _ = print_endline ("shape: " ^ its (elength shaped) ^ 
      " isomorphic variants")
  in
    (elist shaped, shapesize)
  end;

(* -------------------------------------------------------------------------
   Test if a shape is a subgraph of a bigger graph
   ------------------------------------------------------------------------- *)

(* maybe use sparse matrix representation *)
fun subsets_of_size n l = case l of
    [] => if n = 0 then [[]] else []
  | a :: m => 
    let
      val l1 = map (fn subset => a::subset) (subsets_of_size (n - 1) m)
      val l2 = subsets_of_size n m
    in
      l1 @ l2
    end;

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

fun has_shape (shapel,shapesize) msize m =
  let 
    val l = subsets_of_size shapesize (List.tabulate (msize,I))
    fun f subset =
      let 
        val sigma = mk_permf subset
        val candshape = mat_permute (m,shapesize) sigma
      in
        exists (fn x => subcoloring shapesize x candshape) shapel
      end
  in
    exists f l
  end;

fun has_shape_with_edge1 (i,j) (shapel,shapesize) msize m =
  let 
    val l = subsets_of_size shapesize (List.tabulate (msize,I))
    fun f subset =
      if not (mem i subset) then false else
      if not (mem j subset) then false else
      let 
        val sigma = mk_permf subset
        val candshape = mat_permute (m,shapesize) sigma
      in
        exists (fn x => subcoloring shapesize x candshape) shapel
      end
  in
    exists f l
  end;   


fun has_shape_with_edge2 (i,j) (shapel,shapesize) msize m =
  let 
    val l0 = filter (fn x => not (mem x [i,j])) (List.tabulate (msize,I))
    val l1 = subsets_of_size (shapesize-2) l0
    fun f subset =
      let 
        val sigma = mk_permf (i :: j :: subset)
        val candshape = mat_permute (m,shapesize) sigma
      in
        exists (fn x => subcoloring shapesize x candshape) shapel
      end
  in
    exists f l1
  end; 
  
fun keep_only color size m = 
  mat_tabulate (size, fn (i,j) => if mat_sub (m,i,j) = color then 1 else 0)
  
fun has_shape_with_edge3 color (i,j) msize mtop =
  let 
    val shapesize = if color = 1 then !blue_size_glob else !red_size_glob
    val m = keep_only color msize mtop
    val l0 = filter (fn x => not (mem x [i,j])) (List.tabulate (msize,I))
    val l1 = subsets_of_size (shapesize-2) l0
    fun f subset =
      let 
        val sigma = mk_permf (i :: j :: subset)
        val candshape = mat_permute (m,shapesize) sigma
      in
        if color = 1 
        then Array.sub (!blue_array_glob, mat_to_int candshape)
        else Array.sub (!red_array_glob, mat_to_int candshape)
      end
  in
    exists f l1
  end;   
  
  
fun has_shape_with_edge (i,j) (shapel,shapesize) msize m =
  let 
    val b1 = has_shape_with_edge1 (i,j) (shapel,shapesize) msize m
    val b2 = has_shape_with_edge2 (i,j) (shapel,shapesize) msize m
  in
    if b1 = b2 then b1 else 
    raise ERR "has_shape_with_edge" (its i ^ its j)
  end

(* -------------------------------------------------------------------------
   Test if a graph has cycle
   ------------------------------------------------------------------------- *)
 
  
fun neighbor color m x = 
  let fun test y = mat_sub (m,x,y) = color in
    filter test (List.tabulate (mat_size m,I))
  end;
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
  end;
    
fun random_shape_nocycle n color = 
  let val r = random_shape n color in 
    if has_cycle color r then random_shape_nocycle n color else r
  end
  
(* -------------------------------------------------------------------------
   Search (do it for directed graph first because it's easier) 
   select the smallest edge not yet colored.
   ------------------------------------------------------------------------- *)

fun pairbelowy y = List.tabulate (y+1,fn x => (x,y));

(* can also be used to specify the graph shape *)
fun search_order size =
  let 
    val search_order0 = List.concat (List.tabulate (size,fn y => pairbelowy y))
    val search_order1 = filter (fn (x,y) => x <> y) search_order0
    val search_order2 = 
      List.concat (map (fn (x,y) => [(x,y),(y,x)]) search_order1)
  in
    search_order2
  end

(* find all graph of size at most "size" that avoid both shapes *)
(* todo : make it work with mixed colors and a list of shapes *)
(* terrible *)

val counter = ref 0;
val timer = ref (Timer.startRealTimer ());

exception RamseyTimeout;

fun search_one size limit blueshape redshape edgel graph = case edgel of 
    [] => raise ERR "search_step" "no edges"
  | (newi,newj) :: m => 
    let 
      val _ = incr counter
      val _ = case fst limit of
          NONE => ()
        | SOME ti => 
          if !counter > ti then raise RamseyTimeout else ()
      val _ = case snd limit of
          NONE => ()
        | SOME tr => 
          if Timer.checkRealTimer (!timer) > tr then raise RamseyTimeout else ()
      (* depends on the search_order *)
      val csize = Int.max (newi,newj) + 1 
      val bluegraph = mat_tabulate (size, fn (i,j) => 
        if (i,j) = (newi,newj) then 1 else mat_sub (graph,i,j))
      val redgraph = mat_tabulate (size, fn (i,j) => 
        if (i,j) = (newi,newj) then 2 else mat_sub (graph,i,j))
    in
      filter (not o has_shape_with_edge3 1 (newi,newj) csize) [bluegraph] @
      filter (not o has_shape_with_edge3 2 (newi,newj) csize) [redgraph]
    end;
    
fun search_loop size limit blueshape redshape graphl edgel = 
  (
  logp ("edges: " ^ its (length edgel) ^ 
        ", graphs: " ^ its (length graphl) ^ 
        ", steps: " ^ its (!counter))
  ;
  if null graphl then (logp "unsat"; graphl) else
  case edgel of   
    [] => (logp "sat"; graphl)
  | _ :: newedgel => 
    let val newgraphl = 
      List.concat (map (search_one size limit blueshape redshape edgel) graphl)
    in
      search_loop size limit blueshape redshape newgraphl newedgel
    end
  )
  
fun search size limit (blueshape,redshape) =
  let 
    val _ = counter := 0
    val _ = timer := Timer.startRealTimer ()
    val initgraphl = [mat_tabulate (size, fn (i,j) => 0)]
    val initedgel = search_order size
  in
    search_loop size limit (init_shape blueshape) (init_shape redshape) 
      initgraphl initedgel
  end;


(* -------------------------------------------------------------------------
   Graph representations: set of edges, neighbors, adjacency matrices
   ------------------------------------------------------------------------- *)

fun edgecl_to_mat edgecl =
  let 
    val edgel = map fst edgecl
    val edged = dnew (cpl_compare Int.compare Int.compare) edgecl
    val size = list_imax (List.concat (map (fn (a,b) => [a,b]) edgel)) + 1
    fun f (i,j) = case dfindo (i,j) edged of NONE => 0 | SOME c => c 
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
    (edgecl_to_mat (map_assoc (fn _ => 1) (read_edgel blues)),
     edgecl_to_mat (map_assoc (fn _ => 2) (read_edgel reds)))
  end
  
(* -------------------------------------------------------------------------
   Enumerating all supershapes of multiples shape
   ------------------------------------------------------------------------- *)

fun supershapes_one size shape =
  let 
    val edge1l = mat_to_edge1l shape
    val edgel1 = search_order size 
    val edgel2 = filter (fn x => not (mem x (map fst edge1l))) edgel1
    val l1 = cartesian_productl (map (fn x => [(x,0),(x,1)]) edgel2)
    val l2 = map (fn x => edge1l @ x) l1
    val il = map (fn x => mat_to_int (edgecl_to_mat_size size x)) l2
  in
    il
  end;
  
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
  

(*
load "ramsey"; open aiLib kernel ramsey;
val size = 5;
val shape1 = random_shape 5 1;
val shape2 = init_shape shape1;

val a = supershapes shape2;



*)

(* -------------------------------------------------------------------------
   Experiment
   ------------------------------------------------------------------------- *)
  
fun search_each_size limit (blueshape,redshape) =
  let 
    val bluer = init_shape blueshape
    val redr = init_shape redshape
    val _ = blue_array_glob := supershapes bluer
    val _ = red_array_glob := supershapes redr
    val _ = blue_size_glob := snd bluer
    val _ = red_size_glob := snd redr 
    val initsize = Int.max (mat_size blueshape, mat_size redshape) 
    fun loop csize =
      let 
        val _ = logp ("search with graph size: " ^ its csize)  
        val graphl = search csize limit (blueshape,redshape) 
      in
        if null graphl then (true,csize) else loop (csize + 1)
      end
      handle RamseyTimeout => (false,csize) 
  in
    loop initsize 
  end
  
  
fun run expname limit = 
  let
    val expdir = selfdir ^ "/exp/" ^ expname
    val _ = app mkDir_err [selfdir ^ "/exp", expdir]
    val _ = log_file := expdir ^ "/log"
    val filel = listDir (selfdir ^ "/dr100")
    val cnfl = filter (fn x => String.isSuffix "_cnf.p" x) filel
    val brshapel = map_assoc (read_shape o (fn x => "dr100/" ^ x)) cnfl
    fun f ((file,brshape),i) = 
       let 
         val _ = logp ("File " ^ its i ^ ": " ^ file)
         val (r,t) = add_time (search_each_size limit) brshape
         val _ = log ("file time: " ^ rts_round 2 t)
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

fun normalize_naively mat =
  let 
    val size = mat_size mat 
    val fl = map mk_permf (permutations (List.tabulate (size,I)))  
    val matl = map (mat_permute (mat,size)) fl
  in
    hd (dict_sort (array2_compare size) matl)
  end  
  
end (* struct *) 
  
  
(*
load "ramsey"; open aiLib kernel ramsey;
val r = run "ramsey15" (SOME 100000, NONE);

val r = run "ramsey12" (NONE, SOME (Time.fromReal 10.0));
*)

(*
load "ramsey"; open aiLib kernel ramsey;
val filel = listDir (selfdir ^ "/dr100");
val cnfl = filter (fn x => String.isSuffix "_cnf.p" x) filel;
val brshapel = map_assoc (read_shape o (fn x => "dr100/" ^ x)) cnfl;


  
  
  
  
  
  
   
  
  







*)
