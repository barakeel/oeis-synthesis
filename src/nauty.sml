structure nauty :> nauty =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph
val ERR = mk_HOL_ERR "nauty"

(* -------------------------------------------------------------------------
   Nauty algorithm
   ------------------------------------------------------------------------- *)

fun io_neighbors graph x =
  [neighbor_of blue graph x, neighbor_of red graph x]

fun string_of_partition part = 
  String.concatWith "|" (map (String.concatWith " " o map its) part)

fun dpeek x d = Redblackmap.peek (d,x)
fun count_elements arr l =
  let
    fun countHelper [] = ()
      | countHelper (x::xs) = 
        (Array.update (arr, x, Array.sub(arr, x) + 1); countHelper xs)
  in
    countHelper l
  end
 
fun array_compare size a1 a2 i = 
  if i >= size then EQUAL else
  case Int.compare (Array.sub (a1,i),Array.sub (a2,i)) of
    EQUAL => array_compare size a1 a2 (i+1)
  | x => x 

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

fun refine_partition_loop graph ioneighl partl = 
  let
    val graphsize = mat_size graph
    val partl1 = List.concat (map refine_partition partl)
    val partl2 = map (equitable_partition_aux graphsize ioneighl) partl1
    val partl3 = unify_partitions graph graphsize partl2
    val (partl4,partl5) = partition (fn x => length x = graphsize) partl3
  in
    if null partl5 then partl4 
    else partl4 @ refine_partition_loop graph ioneighl partl5
  end

fun nauty_partition graph parttop =
  let
    val graphsize = mat_size graph
    val vertexl = List.tabulate (graphsize,I)
    val ioneighl = map_assoc (io_neighbors graph) vertexl
    val part = equitable_partition_aux graphsize ioneighl parttop
  in
    if length part = graphsize then [part] else 
    refine_partition_loop graph ioneighl [part]
  end
 
fun normalize_nauty_aux graph parttop =
  let
    val graphsize = mat_size graph
    fun f x = (x, mat_permute (graph,graphsize) (mk_permf x))
    val partl = nauty_partition graph parttop
  in
    case partl of [part] => f (List.concat part) | _ =>
      let 
        val perml0 = map List.concat partl
        val matl = map f perml0
      in
        hd (dict_sort (snd_compare (mat_compare_fixedsize graphsize)) matl)
      end
  end

fun normalize_nauty_wperm graph =
  let 
    val vertexl = List.tabulate (mat_size graph,I)
    val (perm,m) = normalize_nauty_aux graph [vertexl]
  in
    (m, perm)
  end
  
fun normalize_nauty graph = 
  let val vertexl = List.tabulate (mat_size graph,I) in 
    snd (normalize_nauty_aux graph [vertexl])
  end

(* -------------------------------------------------------------------------
   Derived functions
   ------------------------------------------------------------------------- *)

fun nauty_set l = mk_fast_set mat_compare (map normalize_nauty l)
 
fun subgraphs m size =   
  let
    val perml = subsets_of_size size (List.tabulate (mat_size m,I))
    val permfl = map mk_permf perml
    val ml = map (mat_permute (m,size)) permfl
  in
    nauty_set ml
  end
 
(*
load "nauty"; open aiLib kernel graph nauty;
val m = random_mat 10;
val (m',perm) = normalize_nauty_wperm m;
val m'' = mat_permute (m',mat_size m') (mk_permf (invert_perm perm));
mat_eq m m'';
*)

end (* struct *)
