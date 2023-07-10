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

(* -------------------------------------------------------------------------
   Adjacency matrix representation
   ------------------------------------------------------------------------- *)

type mat = int Array2.array
fun mat_sub (m,i,j) = Array2.sub (m,i,j)
fun mat_update (m,i,j,v) = Array2.update (m,i,j,v)
fun mat_update_sym (m,i,j,v) =
  (mat_update (m,i,j,v); mat_update (m,j,i,v));
fun mat_tabulate (n,f) = Array2.tabulate Array2.RowMajor (n,n,f)
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
    
(* -------------------------------------------------------------------------
   Neighbor representation (most compact)
   -------------------------------------------------------------------------
*)    
(* -------------------------------------------------------------------------
   Edge representation (fastest to udpate, maybe less garbage collection)
   -------------------------------------------------------------------------
*)   

    
    
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
  
fun has_shape_with_edge (i,j) (shapel,shapesize) msize m =
  let 
    val l0 = filter (fn x => x <> i orelse x <> j) (List.tabulate (msize,I))
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


(* todo: consider changing to a sparse representation (list of edges) 
   for a more efficient update *)
val ERR = mk_HOL_ERR "test";
(* find all graph of size at most "size" that avoid both shapes *)
(* todo : make it work with mixed colors and a list of shapes *)
(* terrible *)

val counter = ref 0;

exception RamseyTimeout;

fun search_one size limit blueshape redshape edgel graph = case edgel of 
    [] => raise ERR "search_step" "no edges"
  | (newi,newj) :: m => 
    let 
      val _ = incr counter
      val _ = if limit > 0 andalso !counter > limit 
              then raise RamseyTimeout
              else ()
      val csize = Int.max (newi,newj) (* depends on the search_order *)
      val bluegraph = mat_tabulate (size, fn (i,j) => 
        if (i,j) = (newi,newj) then 1 else mat_sub (graph,i,j))
      val redgraph = mat_tabulate (size, fn (i,j) => 
        if (i,j) = (newi,newj) then 2 else mat_sub (graph,i,j))
    in
      filter (not o has_shape_with_edge (newi,newj) blueshape csize) 
        [bluegraph] 
      @
      filter (not o has_shape_with_edge (newi,newj) redshape csize) 
        [redgraph]
    end;
    
fun search_loop size limit blueshape redshape graphl edgel = 
  if null graphl then (logp "unsat"; graphl) else
  case edgel of   
    [] => graphl
  | _ :: newedgel => 
    let val newgraphl = 
      List.concat (map (search_one size limit blueshape redshape edgel) graphl)
      val _ = logp (
        "edges: " ^ its (length edgel) ^ 
        ", graphs: " ^ its (length newgraphl) ^ 
        ", steps: " ^ its (!counter))
    in
      search_loop size limit blueshape redshape newgraphl newedgel
    end;
  
fun search size limit (blueshape,redshape) =
  let 
    val _ = counter := 0
    val initgraphl = [mat_tabulate (size, fn (i,j) => 0)]
    val initedgel = search_order size
  in
    search_loop size limit (init_shape blueshape) (init_shape redshape) 
      initgraphl initedgel
  end;

fun search_each_size limit (blueshape,redshape) =
  let 
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
   Experiment
   ------------------------------------------------------------------------- *)
  
fun run expname limit = 
  let
    val expdir = selfdir ^ "/exp/" ^ expname
    val _ = app mkDir_err [selfdir ^ "/exp", expdir]
    val _ = log_file := expdir ^ "/log"
    val filel = listDir "dr100"
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
  
  
end (* struct *) 
  
  
(*
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;

(* val random_subset n allvertex. *)
val blueshape = random_shape_nocycle 4 1;
val redshape = random_shape_nocycle 4 2;

(* one shape *)
val brshape = read_shape "dr100/adr_a_d_rb_inf_cnf.p";

(* bottom-up search *)
val r = run "ramsey2" 100000;






(* simple_search *)
val size = 6;
val (r,t) = add_time (search size blueshape) redshape; 
*)


(*
val size = 8;
val ml = List.tabulate (100, fn _ => symmetrify size (random_mat size));
val (mcl,t) = add_time (map_assoc (charac size)) ml;

fun norm_charac x = dict_sort (snd_compare (list_compare Int.compare)) x;
val mcl1 = map_snd norm_charac mcl;
val mcl2 = map_snd split mcl1;

val mcl3 = map (fn (a,(b,c)) => (c,(a,b))) mcl2;
val mcld = dregroup (list_compare (list_compare Int.compare)) mcl3;

val mcl4 = dlist mcld;
val mcl5 = filter (fn (a,b) => length b > 1) mcl4;

val d = fst (List.nth(mcl5,1));
val (md1,md2) = pair_of_list (snd (List.nth(mcl5,1)));
val (m1,perm1) = md1;
val (m2,perm2) = md2;
fun perm1_f n = List.nth (perm1,n);
fun perm2_f n = List.nth (perm2,n);


all_neighbor size (mat_permute (m1,size) perm1_f);
all_neighbor size (mat_permute (m2,size) perm2_f);

fun misof size (m1,perm1) (m2,perm2) = 
  let 
    fun perm1_f n = List.nth (perm1,n)
    fun perm2_f n = List.nth (perm2,n)
  inval (m1,perm1) = md1;
val (m2,perm2) = md2;
fun perm1_f n = List.nth (perm1,n);
fun perm2_f n = List.nth (perm2,n);
    miso size (m1,perm1_f) (m2,perm2_f)
  end;


val bl = map (uncurry (misof size) o pair_of_list o snd) mcl5;


  
fun split_same [] = []
  | split_same (x::xs) =
    let fun aux xs res =
        case xs of
            [] => [List.rev res]
          | y::ys => if fst y = fst x then aux ys (y::res)
                     else (List.rev res) :: split_same xs
    in aux xs [x]
    end;

(* l is assumed to be ordered (todo rename elements) *)
fun productl l = case l of [] => 1 | a :: m => a * productl m;
map length 

(* normalize with respect to permutations *)
fun stable_permutations l =
  let 
    val l0 = number_snd 0 l
    val l1 = split_same l0
    val l2 = map (map snd) l1
    val i = productl (map length l2)
  in
    if i > 100
    then 
      (print_endline "warning: too many permutations";
       [List.tabulate (length l,I)]) (* todo pick random subsets *)
    else 
      let 
        val l3 = map permutations l2
        val l4 = cartesian_productl l3
    in
      map List.concat l4
    end
  end

val l = stable_permutations d;


fun misofp size perm (m1,perm1) (m2,perm2) = 
  let 
    fun perm1_f n = List.nth (perm1,List.nth(perm,n))
    fun perm2_f n = List.nth (perm2,n)
  in
    miso size (m1,perm1_f) (m2,perm2_f)
  end;

val perm = hd l;

fun test (d,mdl) = 
  let 
    val perml = stable_permutations d  
    val (md1,md2) = pair_of_list mdl
  in
    PolyML.print perml;
    exists (fn permx => misofp size permx md1 md2) perml
  end;
  
val rl = map test mcl5;

(* 
generate all potential permutations 
better/simpler invariants
*)

val nv = all_neighbor (m,5);
val x = all_charac (m,5);
val x' = dict_sort (snd_compare (list_compare Int.compare)) x;
val perm = map fst x';
fun perm_f n = List.nth (perm,n);
*)
(*
val m' = mat_permute (m,5) perm_f;
val mc' = all_charac (m',5);

fun perm_f2 n = List.nth (invpermo,n);

val m2' = mat_permute (m,5) perm_f2;
val m2c' = all_charac (m2',5);
*)
