structure ramsey :> ramsey = struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "ramsey"

val cliquetimemax = ref 1000000

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

val shapetimer = ref 0
exception RamseyTimeout;

(* -------------------------------------------------------------------------
   Tree structure storing all cliques
   ------------------------------------------------------------------------- *) 

datatype tree = Node of int * tree list

val maxd = ref 0

fun add_vertex d f j (Node(i,treel)) =
  if f i 
  then Node(i, add_vertex_treel (d+1) f j treel)
  else Node(i, treel)
   
and add_vertex_treel d f j treel = 
  (
  if d > !maxd then maxd := d else ();
  Node (j,[]) :: map (add_vertex d f j) treel
  )

(* -------------------------------------------------------------------------
   Incrementally adding vertices
   ------------------------------------------------------------------------- *)

fun give_up j = (j >= 3 andalso 
  Math.pow (1.5, Real.fromInt (!maxd)) > Real.fromInt j)

fun next_shapel f (maxj,maxtim) ((btreel,rtreel),bl,j) = 
  if j >= maxj orelse give_up j
    then (j, hash_bl bl) 
  else if !shapetimer >= maxtim
    then raise RamseyTimeout
  else
  let 
    val coloringl = List.tabulate (j, fn i => ([i,j],
      if !rams_diff then f(j-i,0) else f (i,j)))
    val (blueedg,rededg) = partition snd coloringl
    val edgel = map fst (filter snd coloringl)
    val bluev = Vector.fromList (map snd coloringl)
    val redv = Vector.fromList (map (not o snd) coloringl)
    fun fblue x = (incr shapetimer; Vector.sub (bluev,x))
    fun fred x = (incr shapetimer; Vector.sub (redv,x))
    val newbtreel = add_vertex_treel 1 fblue j btreel
    val newrtreel = add_vertex_treel 1 fred j rtreel  
  in
    next_shapel f (maxj,maxtim)
      ((newbtreel,newrtreel), map snd coloringl @ bl, j+1)
  end

fun enum_shapel (maxj,maxtim) f =
  let
    val cache = ref (dempty Int.compare)
    val newf = if not (!rams_diff) then f else
      (
      fn (x,y) => 
        case dfindo x (!cache) of
          NONE => let val r = f(x,y) in
                    cache := dadd x r (!cache); r 
                  end
        | SOME r => r
      )
    val _ = maxd := 0
    val _ = shapetimer := 0
  in
    next_shapel newf (maxj,maxtim) (([],[]),[],0)
  end

fun enum_shapel_err (maxj,maxtim) f =
  let val (sc,hash) = enum_shapel (maxj,maxtim) f in
    SOME (sc,hash)
  end
  handle  
      Empty => NONE
    | Div => NONE
    | ProgTimeout => NONE
    | Overflow => NONE
    | RamseyTimeout => NONE

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
fun exist_clique_v_tim tim n (f:int*int->bool) v l =
  (
  incr shapetimer;
  if !shapetimer > tim then raise RamseyTimeout else ();
  exist_clique_tim tim (n-1) f (filter (fn x => f(v,x)) l)
  )
and exist_clique_tim tim n f l = 
  if n <= 0 then true else
  if length l < n then false else
  exists_withtail (exist_clique_v_tim tim n f) l

fun exist_clique_timer tim n f l =
  (shapetimer := 0;
   exist_clique_tim tim n f l)
  
  
fun all_withtail f l = case l of 
    [] => []
  | a :: m => f a m @ all_withtail f m

fun all_clique_v n (f:int*int->bool) v l =
  map (fn x => v :: x) (all_clique (n-1) f (filter (fn x => f(v,x)) l))

and all_clique n f l = 
  if n = 0 then [[]] else
  if length l < n then [] else
  all_withtail (all_clique_v n f) l
  
(*
load "ramsey"; open ramsey; 
load "aiLib"; open aiLib;

fun f(i,j) = (IntInf.log2 (IntInf.fromInt j - IntInf.fromInt i)) mod 2 <= 0;

fun f (i,j) = j*j mod (2*(i+j)+1) > i+j;
fun mk_sym f (i,j) = if i = j then false
                     else if i < j then f(i,j) else f(j,i); 
val f' = mk_sym f;

val n = 1024
val l = List.tabulate (n,I);
val m = Array2.tabulate Array2.RowMajor (n,n,f');
fun f'' (i,j) = Array2.sub (m,i,j);


fun first_clique_start f n start = 
  let val l = all_clique n f (List.tabulate (start,I)) in
    if null l then first_clique_start f n (start+1) else l
  end;

fun first_clique f n = first_clique_start f n n;
  
val (r,t) = add_time (all_clique 6 f'') (List.tabulate (10,I));
List.tabulate (15, first_clique f'');
List.tabulate (15, first_clique (not o f''));
*)

(*
load "ramsey"; open ramsey; 
load "aiLib"; open aiLib;
fun f (i,j) = j*j mod (2*(i+j)+1) > i+j;
fun mk_sym f (i,j) = if i = j then false
                     else if i < j then f(i,j) else f(j,i); 
val n = 20
val l = List.tabulate (n,I);
val m = Array2.tabulate Array2.RowMajor (n,n,f');

val ERR = mk_HOL_ERR "test";
fun mat_size m = 
  let val (a,b) = Array2.dimensions m in
    if a = b then a else raise ERR "mat_size" ""
  end;
fun mat_sub (m,i,j) = Array2.sub (m,i,j)
fun mat_to_ll m = 
  let val size = mat_size m in
    List.tabulate (size, fn i => List.tabulate (size,fn j => mat_sub (m,i,j)))
  end;

fun color x = if x then "\\x" else " ";
fun color_line l = String.concatWith "& " (map color l);
fun string_of_mat m = String.concatWith "\\\\\n" (map color_line (mat_to_ll m));
fun print_mat m = print_endline (string_of_mat m); 

print_mat m;
*)


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
  
fun exist_clique_mat tim n m = 
  let 
    val l = List.tabulate (mat_size m,I)
    fun f(i,j) = mat_sub (m,i,j) 
  in
    exist_clique_timer tim n f l orelse
    exist_clique_timer tim n (not o f) l
  end

fun hash_mat m = 
  let 
    val bl = ref [] 
    fun f (i,j,x) = bl := (x :: !bl)
  in 
    mat_traverse f m;
    hash_bl (rev (!bl))
  end
  
fun symmetrify m = 
  mat_tabulate (mat_size m, fn (a,b) => 
  if a=b then false else if a < b then mat_sub (m,a,b) else mat_sub (m,b,a));    

fun colorize m = 
  mat_tabulate (mat_size m , fn (a,b) => 
  if a=b then 0 else if mat_sub (m,a,b) then 1 else 2)

fun invert m = 
  mat_tabulate (mat_size m, fn (a,b) => 
  if a=b then false else not (mat_sub (m,a,b)))
  
fun is_nauto m = 
  let 
    val m1 = nauty.normalize_nauty (colorize m)
    val m2 = nauty.normalize_nauty (colorize (invert m)) 
  in 
    graph.mat_eq m1 m2
  end    
 
fun has_expo_clique_f tim f cliquesize = 
  let 
    val graphsize = Real.floor (Math.pow (1.5, Real.fromInt cliquesize)) 
    val m = symmetrify (mat_tabulate (graphsize, 
      fn (i,j) => if i < j then (if !rams_diff then f(j-i,0) else f (i,j)) 
        else false))
  in 
    SOME (exist_clique_mat tim cliquesize m)
    handle  
      Empty => NONE
    | Div => NONE
    | ProgTimeout => NONE
    | Overflow => NONE
    | RamseyTimeout => NONE 
  end
 
fun test_expo_f tim f startsize maxsize =
  if startsize > maxsize then (startsize-1,"finish")
  else case has_expo_clique_f tim f startsize of
      NONE => (startsize-1,"error") 
    | SOME true => (startsize-1,"clique") 
    | SOME false => test_expo_f tim f (startsize+1) maxsize
 
(* todo: we know that 0 is in the clique: maybe optimize for that *)  

fun build_f_wcache p = 
 let
   val _ = push_counter := 0
   val f0 = exec_memo.mk_exec p
   fun f1 (i,j) = (abstimer := 0; timelimit := !timeincr;
      hd (f0 ([IntInf.fromInt i],[IntInf.fromInt j])) > 0)
   val cache = ref (dempty Int.compare)
   val newf = if not (!rams_diff) then f1 else
      (
      fn (x,y) => 
        case dfindo x (!cache) of
          NONE => let val r = f1(x,y) in
                    cache := dadd x r (!cache); r 
                  end
        | SOME r => r
      )
  in 
    newf
  end
  
fun has_expo_clique_p tim p cliquesize = 
  has_expo_clique_f tim (build_f_wcache p) cliquesize 
  
fun test_expo_p tim p startsize maxsize =
  test_expo_f tim (build_f_wcache p) startsize maxsize
  
  
(* -------------------------------------------------------------------------
   Scoring functions
   ------------------------------------------------------------------------- *)

fun double_graph_f graph n f1 = 
  let 
    val size = mat_size graph
    fun f(i,j) = 
      if i >= j 
        then false 
      else if i < size andalso j < size 
        then mat_sub (graph,i,j) 
      else if i >= size andalso j >= size
        then mat_sub (graph,i-size,j-size)
      else if i < size andalso j >= size 
        then f1 (n,i,j-size)
      else raise ERR "ramsey_score_short" ""
    val newgraph = mat_tabulate (2 * size, f)
  in
    symmetrify newgraph
  end

fun double_graph graph n p =
  let 
    val _ = push_counter := 0
    val f0 = exec_memo.mk_exec p
    fun f1 (nloc,i,j) = 
      (
      exec_memo.n_glob := IntInf.fromInt nloc; 
      abstimer := 0; 
      timelimit := !timeincr;
      hd (f0 ([IntInf.fromInt i],[IntInf.fromInt j])) > 0
      )
  in
    SOME (double_graph_f graph n f1) handle  
      Empty => NONE
    | Div => NONE
    | ProgTimeout => NONE
    | Overflow => NONE
  end


val graphsizemax = ref 6  
  
fun test_graph_aux n graph =
  if n < 2 then true else
  if !nauto_check then   
    exist_clique_mat (!cliquetimemax) n graph andalso 
    not (exist_clique_mat (!cliquetimemax) (n+1) graph) andalso
    is_nauto graph
  else
    not (exist_clique_mat (!cliquetimemax) (n+1) graph)  
  
fun test_graph n graph =
  SOME (test_graph_aux n graph) handle RamseyTimeout => NONE
  

  
fun double_graph_loop graph n p = 
  if n >= (!graphsizemax) then SOME (n,hash_mat graph) else
  case double_graph graph n p of
    NONE => NONE 
  | SOME newgraph => 
      (
      case test_graph (n+1) newgraph of
        NONE => NONE
      | SOME false => SOME (n,hash_mat graph)
      | SOME true => double_graph_loop newgraph (n+1) p
      )



(* -------------------------------------------------------------------------
   Give scores to graphs for larger graph sizes.
   ------------------------------------------------------------------------- *)


(*
load "ramsey"; open aiLib kernel ramsey;
cliquetimemax := 1000000000;
timeincr := 10000000;
graphsizemax := 6;

val sol = read_hanabil (selfdir ^ "/exp/ramsey105/hist/itsol38");

val sol = read_hanabil (selfdir ^ "/exp/ramsey12/hist/itsol57");
val progl = map (snd o fst) sol;

val (l1,t) = add_time (map_assoc ramsey_score) progl;
val l2 = filter (not o isSome o snd) l1;
val l3 = map_snd valOf l2;
val l4 = filter (fn x => fst (snd x) < 4) l3;


*)      
      
      
      


(*
load "ramsey"; open ramsey; load "game";
load "human"; val l4 = filter (fn x => fst (snd x) >= 7) l3;
load "aiLib"; open aiLib;
val ERR = mk_HOL_ERR "test";
fun mat_size m = 
  let val (a,b) = Array2.dimensions m in
    if a = b then a else raise ERR "mat_size" ""
  end;
fun mat_sub (m,i,j) = Array2.sub (m,i,j)
fun mat_to_ll m = 
  let val size = mat_size m in
    List.tabulate (size, fn i => List.tabulate (size,fn j => mat_sub (m,i,j)))
  end;
fun color x = if x then "x" else " ";
fun color_line l = String.concatWith " " (map color l);
fun string_of_mat m = String.concatWith "\n" (map color_line (mat_to_ll m));
fun print_mat m = print_endline (string_of_mat m); 


fun f (n,a,b) = 0 > 0;
fun mat_empty n = Array2.array (n,n,false);
fun loop nmax (n,graph) = 
  if n >= nmax then graph else loop nmax (n+1,double_graph_f graph n f);
val graph = loop 1 (0,mat_empty 1);
print_mat graph;
exist_clique_mat 10000000 2 graph;

*)

fun ramsey_score p =
  if !rams_double then double_graph_loop (mat_empty 1) 0 p else
  let 
    val _ = push_counter := 0
    val f0 = exec_memo.mk_exec p
    fun f1 (i,j) = (abstimer := 0; timelimit := !timeincr;
      hd (f0 ([IntInf.fromInt i],[IntInf.fromInt j])) > 0)
  in
    enum_shapel_err (64,2000000) f1
  end


end (* struct *)   

(*
load "human"; open human;
load "ramsey"; open aiLib kernel ramsey;

fun f (a:int,b:int) = (b * b) mod (2*(a+b)+1) > a+b;





val (scl,h) = enum_shapel (32,1000000) f;


fun all 


val sol = read_hanabil (selfdir ^ "/exp/ramsey7/hist/itsol13");
val progl = map (snd o fst) sol;

val maxgraphsize = Real.ceil (27.0 * 1.5);
val maxcliquesize = 8;
val maxtim = 10000000000;

val result = ref []

fun loop (maxgraphsize,maxcliquesize,maxtim) rl = 
  if null rl then () else
  let
    val _ = print_endline ("Searching for graphs of size " ^ 
       its (maxgraphsize - 1) ^ " that do not contain a " ^ 
       its maxcliquesize ^ "-clique")
    fun f p = (p, enum_shapel_p (maxgraphsize-1,maxcliquesize,maxtim) p);
    val (rl0,t) = add_time (map f) (first_n 10000 (rev rl))
    val rl1 = map_snd valOf (filter (isSome o snd) rl0)
    val rl2 = map_snd fst rl1;
    val _ = print_endline (its (length rl2) ^ " programs remaining")
    fun test (a,b) = fst (hd b) < maxcliquesize;
    val rl3 = filter test rl2;
    val _ = print_endline (its (length rl3) ^ " programs remaining in " ^
                           rts_round 2 t ^ " seconds")
    val newmaxgraphsize = Real.ceil (Real.fromInt maxgraphsize * 1.5)
  in
    result := (maxcliquesize,rl3) :: !result;
    loop (newmaxgraphsize,maxcliquesize+1,maxtim) (map fst rl3)
  end;

result := [];
loop (maxgraphsize,maxcliquesize) progl;


fun compare_klevel (klevel1,klevel2) = 
  cpl_compare Int.compare (inv_cmp Int.compare) (hd klevel1, hd klevel2);

val (k,result2) = hd (!result);

val result2' = filter (fn (x,_) => not (contain_opers "divi" x)
                         andalso not (contain_opers "loop" x)) result2;

val result4 = dict_sort (fst_compare prog_compare_size) result2';
val (p,klevel) = hd result4;
human_trivial p;

val maxtim = 100000000000;
result := [];
loop (maxgraphsize,maxcliquesize,maxtim) [p];
val result10 = !result;


val result5 = dict_sort (snd_compare compare_klevel) result2;
val (p,klevel) = hd result5;
human_trivial p;
assoc p result2;

load "aiLib"; open aiLib;
load "graph"; open graph;
fun f2 (i,j) = if f1(i,j) then 1 else 2;
fun mk_sym f (i,j) = if i = j then 0 
                     else if i < j then f(i,j) else f(j,i);
                     
                    
fun f (i,j) = j*j mod (2*(i+j)+1) >= i+j;
fun mk_sym f (i,j) = if i = j then false
                     else if i < j then f(i,j) else f(j,i); 
val f' = mk_sym f;
fun f'' (i,j) = if if f'(i,j) then 1 else 0;
  
fun mat_to_ll m = 
  let val size = mat_size m in
    List.tabulate (size, fn i => List.tabulate (size,fn j => mat_sub (m,i,j)))
  end;

fun color x = if x = 1 then "o" else " ";
fun color_line l = String.concatWith " " (map color l);

fun string_of_mat m = String.concatWith "\n" (map color_line (mat_to_ll m));

fun print_mat m = print_endline (string_of_mat m); 

print_mat (mat_tabulate (64,f''));
print_mat (mat_tabulate (32,f''));
*)

