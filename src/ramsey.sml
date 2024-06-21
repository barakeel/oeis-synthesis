structure ramsey :> ramsey = struct

open HolKernel Abbrev boolLib aiLib dir kernel human
val ERR = mk_HOL_ERR "ramsey"



(* -------------------------------------------------------------------------
   Converting list of booleans to a single arbitrary integer 
   ------------------------------------------------------------------------- *)

val no_hash = ref false

local open IntInf in
fun hash_bl_aux start bl = case bl of 
    [] => start
  | b :: m => hash_bl_aux (2 * start + (if b then 1 else 0)) m;
  
fun hash_bl bl = if !no_hash then 0 else hash_bl_aux 1 bl;  
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

(* -------------------------------------------------------------------------
   Efficiently checking if a graph contains a k-clique or not with a timeout
   ------------------------------------------------------------------------- *)

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
   Heursitically checking if a graph contains a k-clique
   ------------------------------------------------------------------------- *)

fun greedy_clique f clique v maxgraphsize =  
  if v >= maxgraphsize then clique else 
    if all (fn x => f(x,v)) clique 
    then greedy_clique f (v :: clique) (v+1) maxgraphsize
    else greedy_clique f clique (v+1) maxgraphsize 
  
fun random_clique f clique vl =  
  if null vl then clique else 
    let 
      val v = random_elem vl 
      val newclique = v :: clique
      val newvl = filter (fn x => if x = v then false else 
                                  if x < v then f(x,v) else f(v,x)) vl
    in
      random_clique f newclique newvl
    end

fun greedy_random_clique f clique v maxgraphsize =  
  if v >= maxgraphsize then clique else 
    if all (fn x => f(x,v)) clique  andalso random_real () < 0.5
    then greedy_random_clique f (v :: clique) (v+1) maxgraphsize
    else greedy_random_clique f clique (v+1) maxgraphsize;


val cmp_len = cpl_compare (inv_cmp Int.compare) (list_compare Int.compare)

fun smallest_aux cmp best l = case l of 
    [] => best
  | a :: m => if cmp (a,best) = LESS 
              then smallest_aux cmp a m 
              else smallest_aux cmp best m

fun smallest cmp l = case l of 
    [] => raise ERR "smallest" ""
  | a :: m => smallest_aux cmp a m

fun bestfirst_clique width f clique vl =  
  if null vl then clique else 
  let 
    fun g v = 
      let
        val neigh = filter (fn x => if x = v then false else 
                                if x < v then f(x,v) else f(v,x)) vl
      in
        (length neigh,neigh)
      end
    val candl = map_assoc g (random_subset width vl)                          
    val (chosenv,(_,newvl)) = smallest (snd_compare cmp_len) candl
    val newclique = chosenv :: clique
  in
    random_clique f newclique newvl
  end


(*
load "ramsey"; open aiLib kernel ramsey;

fun f (i,j) = j*j mod (2*(i+j)+1) > i+j;

val clique = bestfirst_clique 100 f [] (List.tabulate (1024*1024,I));



val (r,t) = add_time (random_clique f []) (List.tabulate (1024*1024,I));

val r = list_imax (List.tabulate (100, fn _ => 
  length (random_clique f [] (List.tabulate (1024*1024,I))));



fun compare_length (a,b) = cpl_compare (inv_cmp Int.compare) (list_compare Int.compare)
  ((length a, a),(length b, b));

val r = dict_sort compare_length (List.tabulate (100, fn _ => 
  random_clique f [] (List.tabulate (1024*1024,I))));
length (hd r);

val r = dict_sort compare_length (List.tabulate (1, fn _ => 
  greedy_random_clique f [] 0 (1024*1024*1024)));
length (hd r);
average_int (map length r);


64; 1024*1024;



val (r,t) = add_time (greedy_clique f [] 0) (1024*1024);
*)

(* timer *)


  
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

(* -------------------------------------------------------------------------
   Check for cliques and anticliques of increasing sizes
   ------------------------------------------------------------------------- *)

fun is_clique f l = all f (all_pairs l);

val skip_test = ref false
val diagonal_flag = ref true


fun next_minclique (f,m) (maxgraphsize,tim) (cliquesize,anticliquesize) 
  (bl,clique,anticlique) =
  let 
    val prevsize = mat_size m
    val v = Vector.tabulate (prevsize, fn i => 
      if !diagonal_flag then 
        (
        if i mod 2 = 0 
        then f (prevsize-i,0)
        else not (f(prevsize-i,0))
        )
      else f (i,prevsize)
      )
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
      if b1 then (cliquesize,graphsize) :: clique else clique
    val newanticlique = 
      if b2 then (anticliquesize,graphsize) :: anticlique else anticlique
    val newclique' = map (fn (_,x) => x-1) newclique
    val newanticlique' = map (fn (_,x) => x-1) newanticlique
    val newbl = vector_to_list v @ bl
    fun test () = 
      (b1 andalso int_div graphsize (snd (hd clique)) < 1.5) orelse
      (b2 andalso int_div graphsize (snd (hd anticlique)) < 1.5)
  in 
    if not (!skip_test) andalso test ()
      then ((prevsize, hash_bl bl), (clique, anticlique))
    else if graphsize >= maxgraphsize 
      then ((graphsize, hash_bl newbl), (newclique, newanticlique))
    else
      next_minclique (f,m1) (maxgraphsize,tim) 
      (newcliquesize,newanticliquesize) 
      (newbl,newclique,newanticlique)
  end
 
fun mk_cache f = 
  let 
    val d = ref (dempty Int.compare) 
    fun g (k,(u:int)) =
      (
      case dfindo k (!d) of 
        SOME v => v  
      | NONE => 
        let val v = f (k,0) in
          (d := dadd k v (!d); v)
        end
      )
  in
    g                   
  end                         
                           
fun loop_minclique f (maxgraphsize,tim) =
  let val f' = if !diagonal_flag then mk_cache f else f in
    next_minclique (f',mat_empty 1) (maxgraphsize,tim) 
      (2,2) ([],[(1,1)],[(1,1)])
  end
   
fun derive l = case l of
    [] => raise Match
  | [a] => []
  | a :: b :: m => (b-a) :: derive (b :: m)

fun tobinary n = if n = 0 then [] else 
                 if n = 1 then [n] else n mod 2 :: tobinary (n div 2);
fun tobinarylen n = 
  let val l = tobinary n in 
    map IntInf.fromInt (length l :: l)
  end;  
  
val binary_flag = ref false

fun convert i = 
  if !binary_flag then tobinarylen i else [IntInf.fromInt i]

fun timed_prog p = 
  let
    val _ = push_counter := 0
    val f0 = exec_memo.mk_exec p
    fun f1 (i,j) = (abstimer := 0; timelimit := !timeincr;
      hd (f0 (convert i, convert j)) > 0)
  in
    f1
  end
  
(* -------------------------------------------------------------------------
   Parallel execution testing larger sizes and
   returning cliques, anticliques and derivative
   ------------------------------------------------------------------------- *)  

fun write_prog file p = write_progl file [p]
fun read_prog file = hd (read_progl file) 
  
fun write_result file (a,(l1,l2)) =
  writel file [its a, ilts l1, ilts l2]
fun read_result file = 
  let val (s1,s2,s3) = triple_of_list (readl_empty file) in
    (string_to_int s1, (stil s2, stil s3))
  end
  
fun execspec_fun () p =
  let 
    val f = timed_prog p
    val default = (0,([],[]))
    fun transform l = map (fn (_,x) => x-1) (rev l)
  
  in
    let val ((a,b),(c,d)) = loop_minclique f (1024,1000000000) in
      (a,(transform c,transform d))
    end
    handle  
      Empty => default
    | Div => default
    | ProgTimeout => default
    | Overflow => default
    | RamseyTimeout => default
  end

fun write_noparam (_:string) () = ()
fun read_noparam (_:string) = ()

val execspec : (unit, prog, int * (int list * int list)) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "ramsey.execspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir),
     "ramsey.no_hash := true"  
    ] 
    ^ ")"),
  function = execspec_fun,
  write_param = write_noparam,
  read_param = read_noparam,
  write_arg = write_prog,
  read_arg = read_prog,
  write_result = write_result,
  read_result = read_result
  }



fun parallel_exec expname =
  let  
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = mkDir_err dir
    val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val sol = read_hanabil (dir ^ "/input")
    val pl = map (snd o fst) sol;
    val (rl,t) = add_time 
      (smlParallel.parmap_queue_extern ncore execspec ()) pl
    val prl = combine (pl,rl)
    val prl1 = filter (fn (_,(sc,_)) => sc > 0) prl
    val prl2 = map (fn (p,(sc,b)) => (p,((sc,prog_size p),b))) prl1
    val cmp = fst_compare (cpl_compare (inv_cmp Int.compare) Int.compare)
    val prl3 = dict_sort (snd_compare cmp) prl2
    fun f (p,((sc,size),(clique,anticlique))) =
      let
        val clique' = derive clique
        val anticlique' = derive anticlique
      in
        String.concatWith "\n"
        [its sc ^ " | " ^ its size,
         human_trivial p ^ " | " ^ gpt_of_prog p,
         ilts clique,
         ilts clique',
         ilts anticlique,
         ilts anticlique']
      end
  in
    writel (dir ^ "/log") ["time: " ^ rts t];
    writel (dir ^ "/output") (map f prl3)
  end  

(*
cd oeis-synthesis/src/exp
mkdir ramsey17extra;
cp ramsey17/hist/itsol16 ramsey17extra/input
load "ramsey"; open ramsey;
parallel_exec "ramsey17extra";

cd oeis-synthesis/src/exp
mkdir ramsey18extra
cp ramsey18/hist/itsol70 ramsey18extra/input
cd ..
load "ramsey"; open ramsey;
parallel_exec "ramsey18extra";

cd oeis-synthesis/src/exp
mkdir ramsey20extra
cp ramsey20/hist/itsol9 ramsey20extra/input
cd ..
sh hol.sh
load "ramsey"; open ramsey;
parallel_exec "ramsey20extra";

*)

(* -------------------------------------------------------------------------
   Ranking programs according to their scores
   ------------------------------------------------------------------------- *)

fun ramsey_score p = 
  let 
    val f = timed_prog p 
  in
    SOME (fst (loop_minclique f (128,100000000))) 
    handle  
      Empty => NONE
    | Div => NONE
    | ProgTimeout => NONE
    | Overflow => NONE
    | RamseyTimeout => NONE 
  end

(*
load "ramsey"; open ramsey; 
load "aiLib"; open aiLib;
fun f (i,j) = j*j mod (2*(i+j)+1) > i+j;
skip_test := true;
no_hash := true;

val ((sc,(a,b)),t) = add_time (loop_minclique f) (1024,100000000);
 
fun rate l = case l of
    [] => raise Match
  | [a] => []
  | a :: b :: m => (int_div b a) :: rate (b :: m);
 
val newclique' = rev (map (fn (_,x) => x-1) a);
val newanticlique' = rev (map (fn (_,x) => x-1) b);

val ratel1 = rate (tl newclique');
val ratel2 = rate (tl newanticlique');

fun f x = 
  






fun f (i,j) = (((((2-i) mod j) div 2) div 2) - j) mod 2 <= 0;

val clique = map (fn (_,x) => x-1) (rev a);
val anticlique = map (fn (_,x) => x-1) (rev b);
derive clique;
derive anticlique;  

val a =
   [(1, 1), (2, 3), (3, 6), (4, 8), (5, 20), (6, 27), (7, 43), (8, 67),
    (9, 91)]: (int * int) list
val b =
   [(1, 1), (2, 2), (3, 4), (4, 10), (5, 14), (6, 22), (7, 33), (8, 59),
    (9, 89), (10, 118)]: (int * int) list
val t = 0.039823: real



*)



end (* struct *)   



