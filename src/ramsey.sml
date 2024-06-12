structure ramsey :> ramsey = struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "ramsey"



(* -------------------------------------------------------------------------
   Converting list of booleans to a single arbitrary integer 
   ------------------------------------------------------------------------- *)

local open IntInf in
fun hash_bl_aux start bl = case bl of 
    [] => start
  | b :: m => hash_bl_aux (2 * start + (if b then 1 else 0)) m;
  
fun hash_bl bl = hash_bl_aux 1 bl;  
end;
 
(* -------------------------------------------------------------------------
   Limit the number of operations when checking cliques
   ------------------------------------------------------------------------- *)  

val cliquetimer = ref 0
exception RamseyTimeout;

(* -------------------------------------------------------------------------
   Efficiently checking if a graph contains a k-clique or not
   ------------------------------------------------------------------------- *)

fun exists_withtail f l = case l of 
    [] => false
  | a :: m => f a m orelse exists_withtail f m

fun exist_clique_v n (f:int*int->bool) v l =
  exist_clique (n-1) f (filter (fn x => f(v,x)) l)
  
and exist_clique n f l = 
  if n = 0 then true else
  if length l < n then false else
  exists_withtail (exist_clique_v n f) l

(* timer *)

fun check_cliquetimer tim = 
  (incr cliquetimer; if !cliquetimer > tim then raise RamseyTimeout else ())
  
fun exist_clique_v_tim tim n (f:int*int->bool) v l =
  (
  check_cliquetimer tim;
  exist_clique_tim tim (n-1) f (filter (fn x => f(v,x)) l)
  )
and exist_clique_tim tim n f l = 
  if n <= 0 then true else
  if length l < n then false else
  exists_withtail (exist_clique_v_tim tim n f) l

fun exist_clique_timer tim n f l =
  (cliquetimer := 0; exist_clique_tim tim n f l)
 
fun exist_clique_v_timer tim n f l =
  (cliquetimer := 0; exist_clique_v_tim tim n f l) 
  
(* -------------------------------------------------------------------------
   Matrice short cuts
   ------------------------------------------------------------------------- *)

fun mat_sub (m,i,j) = Array2.sub (m,i,j)
fun mat_update (m,i,j,x) = Array2.update(m,i,j,x)
fun mat_update_sym (m,i,j,x) = 
  (mat_update (m,i,j,x); mat_update (m,j,i,x))
fun mat_empty n = Array2.array (n,n,false);
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

fun invert m = 
  mat_tabulate (mat_size m, fn (a,b) => 
  if a=b then false else not (mat_sub (m,a,b)))

(* -------------------------------------------------------------------------
   Preparting a function for fast clique testing
   (essentially pre-computing the adjacacency matrix)
   ------------------------------------------------------------------------- *)

fun extend_mat m v = 
  let
    val n = mat_size m
    fun f(i,j) = 
      if i = j then false else
      if i < n andalso j < n then (mat_sub (m,i,j)
        handle Subscript => raise ERR "m" (its i ^ "-" ^ its j))
      else if i = n then (Vector.sub (v,j) 
        handle Subscript => raise ERR "v" (its j))
      else if j = n then (Vector.sub (v,i) 
        handle Subscript => raise ERR "v" (its i))
      else raise ERR "extend_mat" ""
  in
    Array2.tabulate Array2.RowMajor (n+1,n+1,f)
  end 

fun derive l = case l of
    [] => raise ERR "derive" "empty"
  | [a] => []
  | a :: b :: m => (b-a) :: derive (b :: m)

(* -------------------------------------------------------------------------
   Check for cliques and anticliques of increasing sizes
   ------------------------------------------------------------------------- *)

fun next_minclique (f,m) (maxgraphsize,tim) (cliquesize,anticliquesize) 
  (clique,anticlique) = 
  if mat_size m >= maxgraphsize then (rev clique, rev anticlique) else
  let 
    val prevsize = mat_size m
    val v = Vector.tabulate (prevsize, fn i => f (i,prevsize))
    val m1 = extend_mat m v
    val graphsize = mat_size m1
    val m2 = invert m1
    fun f1 (i,j) = Array2.sub (m1,i,j)
    fun f2 (i,j) = Array2.sub (m2,i,j)
    val vl = rev (List.tabulate (graphsize,I))
    val b1 = exist_clique_v_timer tim cliquesize f1 (hd vl) (tl vl)
    val b2 = exist_clique_v_timer tim anticliquesize f2 (hd vl) (tl vl)
    val newcliquesize = if b1 then cliquesize + 1 else cliquesize
    val newanticliquesize = if b2 then anticliquesize + 1 else anticliquesize
    val newclique = 
      if b1 
      then (cliquesize,graphsize) :: clique 
      else clique
    val newanticlique = 
      if b2 
      then (anticliquesize,graphsize) :: anticlique
      else anticlique
  in
    next_minclique (f,m1) (maxgraphsize,tim) 
      (newcliquesize,newanticliquesize) 
      (newclique,newanticlique)
  end
  
fun loop_minclique f (maxgraphsize,tim) =
  next_minclique (f,mat_empty 1) (maxgraphsize,tim) (2,2) ([(1,1)],[(1,1)])
  
(*
load "ramsey"; open ramsey; 
load "aiLib"; open aiLib;
fun f (i,j) = j*j mod (2*(i+j)+1) > i+j;
val ((a,b),t) = add_time (loop_minclique f) (128,100000000);

val a =
   [(1, 1), (2, 3), (3, 6), (4, 8), (5, 20), (6, 27), (7, 43), (8, 67),
    (9, 91)]: (int * int) list
val b =
   [(1, 1), (2, 2), (3, 4), (4, 10), (5, 14), (6, 22), (7, 33), (8, 59),
    (9, 89), (10, 118)]: (int * int) list
val t = 0.039823: real
*)

fun timed_prog p = 
  let
    val _ = push_counter := 0
    val f0 = exec_memo.mk_exec p
    fun f1 (i,j) = (abstimer := 0; timelimit := !timeincr;
      hd (f0 ([IntInf.fromInt i],[IntInf.fromInt j])) > 0)
  in
    f1
  end
  
fun ramsey_score p = (0,[]) 
  (* loop_minclique f (64,100000000) (timed_prog p) *)



end (* struct *)   



