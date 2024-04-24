structure graph :> graph =
struct   

open HolKernel Abbrev boolLib aiLib kernel smlParallel
val ERR = mk_HOL_ERR "graph"

type mat = int Array2.array
type coloring = ((int * int) * int) list

val blue = 1
val red =2

(* -------------------------------------------------------------------------
   Array2 shortcuts
   ------------------------------------------------------------------------- *)

fun mat_sub (m,i,j) = Array2.sub (m,i,j)
fun mat_update (m,i,j,x) = Array2.update(m,i,j,x)
fun mat_update_sym (m,i,j,x) = 
  (mat_update (m,i,j,x); mat_update (m,j,i,x))

fun mat_empty n = Array2.array (n,n,0);

fun mat_tabulate (n,f) = Array2.tabulate Array2.RowMajor (n,n,f)
 
fun mat_traverse f m = 
  let 
    val range = {base=m,row=0,col=0,nrows=NONE,ncols=NONE}
    fun g (i,j,x) = if i < j then f (i,j,x) else ()
  in
    Array2.appi Array2.RowMajor g range
  end 

fun mat_size m = 
  let val (a,b) = Array2.dimensions m in
    if a = b then a else raise ERR "mat_size" ""
  end
  
fun mat_copy graph = 
  let fun f (i,j) = mat_sub (graph,i,j) in
    mat_tabulate (mat_size graph, f)
  end  

(* -------------------------------------------------------------------------
   Helpers for undirected graphs
   ------------------------------------------------------------------------- *)
  
fun symmetrify m = 
  mat_tabulate (mat_size m, fn (a,b) => 
  if a=b then 0 else if a < b then mat_sub (m,a,b) else mat_sub (m,b,a));  
  
(* -------------------------------------------------------------------------
   Comparison functions
   ------------------------------------------------------------------------- *)

val edge_compare = cpl_compare Int.compare Int.compare  

fun mat_compare_aux size a1 a2 i j = 
  case Int.compare (mat_sub (a1,i,j),mat_sub (a2,i,j)) of
      EQUAL => if j >= size - 1 then 
                 if i >= size - 1 
                 then EQUAL 
                 else mat_compare_aux size a1 a2 (i+1) 0
               else mat_compare_aux size a1 a2 i (j+1)
    | r => r;


fun mat_compare (a1,a2) = 
  case Int.compare (mat_size a1, mat_size a2) of
    EQUAL => mat_compare_aux (mat_size a1) a1 a2 0 0
  | x => x 

fun mat_eq a1 a2 = mat_compare (a1,a2) = EQUAL

(* same as mat_compare but faster if the size are equal *)
fun mat_compare_fixedsize size (a1,a2) = mat_compare_aux size a1 a2 0 0  
    
val mat_set = mk_fast_set mat_compare

(* -------------------------------------------------------------------------
   Initialization
   ------------------------------------------------------------------------- *)

fun random_mat size = symmetrify
  (mat_tabulate (size,fn (a,b) => if a=b then 0 else random_int (0,2)));

fun random_full_mat size = symmetrify
  (mat_tabulate (size,fn (a,b) => if a=b then 0 else random_int (1,2)));

fun matK size = 
  mat_tabulate (size,fn (a,b) => if a=b then 0 else 1);
 
fun matKn size n = 
  mat_tabulate (size + 1, fn (a,b) => 
    if (a = size andalso b >= n) orelse 
       (b = size andalso a >= n) orelse (a=b) 
    then 0 else 1);

(* -------------------------------------------------------------------------
   Neighbors
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   Debug
   ------------------------------------------------------------------------- *)

fun string_of_edgel edgel = 
  let fun f (i,j)= its i ^ "-" ^ its j in
    String.concatWith " " (map f edgel)
  end

fun string_of_edgecl edgecl = 
  let fun f ((i,j),x) = its i ^ "-" ^ its j ^ ":" ^ its x in
    String.concatWith " " (map f edgecl)
  end

fun named_neighbor color graph = 
  let
    val l1 = number_fst 0 (all_neighbor color graph) 
    fun g (i,l) = (i, filter (fn x => x > i) l)
    val l2 = map g l1
  in
    filter (not o null o snd) l2
  end

fun string_of_graph graph = 
  let fun f (i,l) = its i ^ "-" ^ String.concatWith "_" (map its l) in
    String.concatWith " " (map f (named_neighbor blue graph)) ^ " | " ^
    String.concatWith " " (map f (named_neighbor red graph))
  end

fun string_of_bluegraph graph = 
  let fun f (i,l) = its i ^ "-" ^ String.concatWith "_" (map its l) in
    String.concatWith ", " (map f (named_neighbor blue graph))
  end
  
fun mat_to_ll m = 
  let val size = mat_size m in
    List.tabulate (size, fn i => List.tabulate (size,fn j => mat_sub (m,i,j)))
  end

fun string_of_mat m = String.concatWith "\n" (map ilts (mat_to_ll m))

fun print_mat m = print_endline (string_of_mat m); 
  

(* -------------------------------------------------------------------------
   Switching between representations
   todo: store the size at the beginning of a edgecl for easier reconstruction
   ------------------------------------------------------------------------- *)

fun mat_to_edgecl m =
  let 
    val l = ref []
    fun f (i,j,x) = if x <> 0 then l := ((i,j),x) :: !l else ()      
  in
    mat_traverse f m; rev (!l)
  end  

fun edgecl_to_mat size edgecl =
  let 
    val edgel = map fst edgecl
    val edged = dnew (cpl_compare Int.compare Int.compare) edgecl
    fun f (i,j) = case dfindo (i,j) edged of NONE => 0 | SOME c => c 
  in
    symmetrify (mat_tabulate (size, f))
  end

(* -------------------------------------------------------------------------
   Create diagonal by block matrix and reduce the set of ramsey clauses
   ------------------------------------------------------------------------- *)

fun shift_edgecl x ecl = map (fn ((a,b),c) => ((a + x, b + x),c)) ecl;

fun diag_mat m1 m2 = 
  let
    val ecl1 = mat_to_edgecl m1
    val ecl2 = shift_edgecl (mat_size m1) (mat_to_edgecl m2)
    val m = edgecl_to_mat (mat_size m1 + mat_size m2) (ecl1 @ ecl2)
  in
    m
  end

(* -------------------------------------------------------------------------
   Graph I/O
   ------------------------------------------------------------------------- *)

fun find_size i ln = 
  if i > 10000 then raise ERR "find_size" "size > 10000" else
  if i * (i-1) div 2 = ln then i else find_size (i+1) ln

local open IntInf in

fun zip_mat m = 
  let 
    val r = ref 1
    fun f (i,j,x) = r := !r * 3 + IntInf.fromInt x
  in
    mat_traverse f m; !r
  end

fun all_edges size =
  let 
    val m = mat_tabulate (size, fn _ => 0)
    val r = ref []
    fun f (i,j,x) = r := (i,j) :: !r
  in
    mat_traverse f m;
    rev (!r)
  end    

fun unzip_mat mati =
  let 
    fun loop x = if x < 3 then [] else x mod 3 :: loop (x div 3) 
    val l1 = rev (loop mati)
    val size = find_size 1 (length l1)
    val l2 = all_edges size
    val edgecl = combine (l2, map IntInf.toInt l1)
  in
    edgecl_to_mat size edgecl
  end      
  
end (* local *)

fun szip_mat m = IntInf.toString (zip_mat m)
fun sunzip_mat s = unzip_mat (valOf (IntInf.fromString s))


local open IntInf in

fun zip_full m =
  let 
    val r = ref 1 
    fun f (i,j,x) = r := !r * 2 + (if x = blue then 1 else 0) 
  in
    mat_traverse f m; !r
  end

fun unzip_full size mati =
  let 
    fun loop x = if x < 2 then [] else x mod 2 :: loop (x div 2) 
    val l1 = rev (loop mati)
    val l2 = all_edges size
    val edgecl0 = combine (l2, map IntInf.toInt l1)
    val edgecl1 = map_snd (fn b => if b = 1 then blue else red) edgecl0
  in
    edgecl_to_mat size edgecl1
  end
  
fun unzip_full_edgecl size mati =
  let 
    fun loop x = if x < 2 then [] else x mod 2 :: loop (x div 2) 
    val l1 = rev (loop mati)
    val l2 = all_edges size
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

fun extend_mat m n = edgecl_to_mat (mat_size m + 2) (mat_to_edgecl m)

fun mat_permute (m,size) sigma =
  let fun f (x,y) = mat_sub (m, sigma x, sigma y) in
    mat_tabulate (size, f)
  end
 
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
  
fun invert_perm perm = 
  let val permd = dnew Int.compare (number_snd 0 perm) in
    List.tabulate (dlength permd, fn i => dfind i permd)
  end 
  
fun random_subgraph subsize m =
  let
    val vertexl = List.tabulate (mat_size m,I)
    val perm = random_elem (subsets_of_size subsize vertexl)
    val permf = mk_permf perm
  in
    mat_permute (m,subsize) permf
  end

(* -------------------------------------------------------------------------
   Generalizations and colorings
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

(* -------------------------------------------------------------------------
   Properties
   ------------------------------------------------------------------------- *)

fun number_of_edges m = 
  let 
    val y = ref 0 
    fun f (i,j,x) = if x <> 0 then incr y else ()
  in
    mat_traverse f m; 
    !y
  end

fun number_of_blueedges m = 
  let 
    val y = ref 0 
    fun f (i,j,x) = if x = 1 then incr y else ()
  in
    mat_traverse f m; 
    !y
  end  

fun number_of_holes m = 
  let 
    val y = ref 0 
    fun f (i,j,x) = if x = 0 then incr y else ()
  in
    mat_traverse f m;  !y
  end

fun all_holes m = 
  let 
    val l = ref [] 
    fun f (i,j,x) = if x = 0 then l := (i,j) :: !l else ()
  in
    mat_traverse f m; !l
  end
  
fun all_cedges m = 
  let 
    val l = ref [] 
    fun f (i,j,x) = if x <> 0 then l := (i,j) :: !l else ()
  in
    mat_traverse f m; !l
  end 

fun is_ramsey (bluen,redn) topm = 
  let 
    val vertexl = List.tabulate (mat_size topm,I)
    val bluem = mat_copy topm 
    fun f (i,j,x) = if x = 0 then mat_update_sym (bluem,i,j,blue) else ()
    val _ = mat_traverse f topm
    val redm = mat_copy topm
    fun f (i,j,x) = if x = 0 then mat_update_sym (redm,i,j,red) else ()
    val _ = mat_traverse f topm
    fun is_clique m color l = 
      let val l' = map pair_of_list (subsets_of_size 2 l) in
        all (fn (a,b) => mat_sub (m,a,b) = color) l'
      end
  in
    not (exists (is_clique bluem blue) (subsets_of_size bluen vertexl)) andalso
    not (exists (is_clique redm red) (subsets_of_size redn vertexl)) 
  end



end (* struct *)
