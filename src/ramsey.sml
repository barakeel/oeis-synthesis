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

val shapetimer = ref 0   
exception RamseyTimeout;

(* -------------------------------------------------------------------------
   Tree structures storing all cliques
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

fun give_up j = j > 3 andalso 
  j < Real.ceil (Math.pow (1.414, Real.fromInt (!maxd)))
  
fun next_shapel f (maxj,maxtim) ((btreel,rtreel),bl,scl,j) = 
  if j >= maxj
    then (scl, hash_bl bl) 
  else if give_up j orelse !shapetimer >= maxtim
    then raise RamseyTimeout
  else
  let 
    val coloringl = List.tabulate (j, fn i => ([i,j],f (i,j)))
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
      ((newbtreel,newrtreel), map snd coloringl @ bl, !maxd :: scl, j+1)
  end

fun enum_shapel (maxj,maxtim) f =
  let
    val _ = maxd := 0
    val _ = shapetimer := 0
  in
    next_shapel f (maxj,maxtim) (([],[]),[],[],0)
  end

fun enum_shapel_err (maxj,maxtim) f =
  let val (scl,hash) = enum_shapel (maxj,maxtim) f in
    SOME (~ (sum_int scl), hash)
  end
  handle  
      Empty => NONE
    | Div => NONE
    | ProgTimeout => NONE
    | Overflow => NONE
    | RamseyTimeout => NONE

fun ramsey_score p =
  let 
    val _ = push_counter := 0
    val f0 = exec_memo.mk_exec p
    fun f1 (i,j) = (abstimer := 0; timelimit := !timeincr;
      hd (f0 ([IntInf.fromInt i],[IntInf.fromInt j])) > 0)
  in
    enum_shapel_err (32,1000000) f1
  end


end (* struct *)   

(*
load "human"; open human;
load "ramsey"; open aiLib kernel ramsey;

fun f (a:int,b:int) = (b * b) mod (2*(a+b)+1) > a+b;
val (scl,h) = enum_shapel (32,1000000) f;





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

load "graph"; open graph;
fun f2 (i,j) = if f1(i,j) then 1 else 2;
fun mk_sym f (i,j) = if i = j then 0 
                     else if i < j then f(i,j) else f(j,i);
                     
                    





  
fun mat_to_ll m = 
  let val size = mat_size m in
    List.tabulate (size, fn i => List.tabulate (size,fn j => mat_sub (m,i,j)))
  end;

fun color x = if x = 1 then "o" else " ";
fun color_line l = String.concatWith " " (map color l);

fun string_of_mat m = String.concatWith "\n" (map color_line (mat_to_ll m));

fun print_mat m = print_endline (string_of_mat m); 

print_mat (mat_tabulate (40, mk_sym f2));

*)

