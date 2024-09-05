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
   Arithmetical functions
   ------------------------------------------------------------------------- *)  

fun remove_div a m = filter (fn x => x mod a <> 0) m;

fun get_primes acc l = case l of 
    [] => rev acc 
  | a :: m => get_primes (a :: acc) (remove_div a m);
  
fun primes_leq n = get_primes [] (List.tabulate (n-1, fn x => x + 2));

fun all_squares_mod b =
  if b = 0 
  then enew Int.compare [] 
  else enew Int.compare (map (fn x => (x * x) mod b) (List.tabulate (b,I)));

fun create_is_square_mod vn = 
  let
    val all_squares = Vector.tabulate (vn,all_squares_mod);
    fun is_square_mod (a,b) = if b = 0 then false 
      else emem (a mod b) (Vector.sub (all_squares,b));
    val m = Array2.tabulate Array2.RowMajor (vn, vn, is_square_mod);
  in
    fn (a,b) => Array2.sub (m,a,b)
  end;

(* -------------------------------------------------------------------------
   Efficiently checking if a graph contains a k-clique or not
   ------------------------------------------------------------------------- *)

fun exist_withtail f l = case l of 
    [] => false
  | a :: m => f a m orelse exist_withtail f m

fun exist_clique_v n f v l =
  exist_clique (n-1) f (filter (fn x => f(v,x)) l)
  
and exist_clique n f l = 
  if n = 0 then true else
  if length l < n then false else
  exist_withtail (exist_clique_v n f) l
  
(* -------------------------------------------------------------------------
   Finding maximum clique
   ------------------------------------------------------------------------- *)

val cliquemax = ref 0

fun app_withtail f l = case l of 
    [] => ()
  | a :: m => (f a m; app_withtail f m)

fun max_clique_v cliquen f v l =
  max_clique_aux (cliquen + 1) f (filter (fn x => f(v,x)) l)
  
and max_clique_aux cliquen f l = 
  if null l then 
    (if cliquen > !cliquemax then cliquemax := cliquen else ())
  else if cliquen + length l <= !cliquemax then ()
  else app_withtail (max_clique_v cliquen f) l
 
fun max_clique f l = (cliquemax := 0; max_clique_aux 0 f l; !cliquemax)

fun max_clique_both (n,f) = 
  let val vl = tl (List.tabulate (n,I)) in
    Int.max (max_clique f vl, max_clique (not o f) vl)
  end
 
fun max_clique_both0 (n,f) = 
  let 
    val vl = tl (List.tabulate (n,I))
    val vl1 = filter (fn x => f(0,x)) vl
    val vl2 = filter (fn x => not(f(0,x))) vl
  in
    1 + Int.max (max_clique f vl1, max_clique (not o f) vl2)
  end

(* -------------------------------------------------------------------------
   List all cliques of size n
   ------------------------------------------------------------------------- *)

fun all_withtail f l = case l of 
    [] => []
  | a :: m => f a m @ all_withtail f m

fun all_clique_v n f v l =
  map (fn x => v :: x) (all_clique (n-1) f (filter (fn x => f(v,x)) l))

and all_clique n f l = 
  if n = 0 then [[]] else
  if length l < n then [] else
  all_withtail (all_clique_v n f) l;  

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
  exist_withtail (exist_clique_v_tim tim n f) l

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

(* -------------------------------------------------------------------------
   Matrice short cuts
   ------------------------------------------------------------------------- *)

fun mat_sub (m,i,j) = Array2.sub (m,i,j)
fun mat_update (m,i,j,x) = Array2.update(m,i,j,x)
fun mat_update_sym (m,i,j,x) = 
  (mat_update (m,i,j,x); mat_update (m,j,i,x))
fun mat_empty n = Array2.array (n,n,false);
fun mat_tabulate (n, (f:int * int -> bool)) = 
  Array2.tabulate Array2.RowMajor (n,n,f)
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

fun mat_bti m = graph.mat_tabulate (mat_size m, fn (x,y) => if
  mat_sub (m,x,y) then 1 else 0) 
fun mat_itb m = mat_tabulate (graph.mat_size m, fn (x,y) => if
  graph.mat_sub (m,x,y) > 0 then true else false)

fun invert m = 
  mat_tabulate (mat_size m, fn (a,b) => 
    if a=b then false else not (mat_sub (m,a,b)))

fun mat_to_ll m = 
  let val size = mat_size m in
    List.tabulate (size, fn i => List.tabulate (size,fn j => mat_sub (m,i,j)))
  end

fun blts l = String.concatWith " " (map (fn x => if x then "1" else "0") l)

fun string_of_mat m = String.concatWith "\n" (map blts (mat_to_ll m))

fun print_mat m = print_endline (string_of_mat m); 

(* -------------------------------------------------------------------------
   Generating clauses
   ------------------------------------------------------------------------- *)

fun random_clause n = List.tabulate (2*n, fn _ => random_int (~1,1));   
   
fun frombin_aux acc l = case l of 
[] => acc
  | a :: m => frombin_aux (2 * acc + a) m

fun frombin l = frombin_aux 0 l;
   
fun edgel_of_clause clause = 
  let 
    val nvar = length clause div 2
    val (clause1,clause2) = part_n nvar clause 
    fun f x = if x = 0 then [0,1] else if x > 0 then [1] else [0]
    val clause1' = cartesian_productl (map f clause1) 
    val l1 = map frombin clause1'
    val clause2' = cartesian_productl (map f clause2)
    val l2 = map frombin clause2'
  in
    filter (fn (x,y) => x < y) (cartesian_product l1 l2)
  end;

fun update_edge m (i,j) = mat_update_sym (m,i,j,true);
fun update_edgel m edgel = app (update_edge m) edgel;


fun gen_lit (f:int-> int -> int -> IntInf.int) varn clausei vari =
  let val x = f varn clausei vari in
    if x = 0 then 0 else if x > 0 then 1 else ~1
  end
  
fun gen_clause f varn clausei =
  let val varl = 
    List.tabulate (varn, fn x => ~(x+1)) @ List.tabulate (varn, fn x => x+1)
  in
    map (gen_lit f varn clausei) varl
  end

fun pass_clausel bl tim f varn = 
  let
    val vl = List.tabulate (int_pow 2 varn,I)
    val m = mat_empty (int_pow 2 varn)
    fun loop clausei = 
      if clausei >= varn*varn then () else 
      let 
        val clause = gen_clause f varn clausei
        val edgel = edgel_of_clause clause
        val _ = update_edgel m edgel
      in
        loop (clausei+1)
      end
    val _ = loop 0
    fun g (i,j,b) = bl := b :: !bl
    val _ = mat_traverse g m
    fun f (i,j) = mat_sub (m,i,j)
  in
    if exist_clique_timer tim (2*varn+1) f vl then false
    else if exist_clique_timer tim (2*varn+1) (not o f) vl then false
    else true
  end
  handle 
      Empty => false
    | Div => false
    | ProgTimeout => false
    | Overflow => false
    | RamseyTimeout => false

  
fun loop_pass_clausel bl f (varn,maxvarn,tim) =
  if varn > maxvarn then maxvarn else 
  if pass_clausel bl tim f varn 
  then loop_pass_clausel bl f (varn+1,maxvarn,tim)
  else varn - 1

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
      (b1 andalso int_div graphsize (snd (hd clique)) < 1.414) orelse
      (b2 andalso int_div graphsize (snd (hd anticlique)) < 1.414)
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
  
(*
load "aiLib"; open aiLib;
load "ramsey"; open ramsey;
load "graph";
load "nauty"; open nauty;



val is_square_mod = create_is_square_mod 1024;

fun paley_graph p =
  let fun f (a,b) = if a = b then false 
                    else is_square_mod ((a - b) mod p, p) in
    mat_bti (mat_tabulate (p,f))
  end;

fun neighbor_graph p =
  let 
    fun f (a,b) = is_square_mod ((a - b) mod p, p)
    val vl = List.tabulate (p,I)
    val neighborl = filter (fn x => f(0,x)) (tl vl)
  in
    graph.mat_permute (paley_graph p, length neighborl) 
      (graph.mk_permf neighborl)
  end;


val m = paley_graph 17;
graph.print_mat m;
val m' = neighbor_graph 17;
graph.print_mat m';

val m' = Array2.tabulate Array2.RowMajor 
  (8,8, fn (x,y) => if mat_sub (m,x,y) then 1 else 0);
print_mat m;

val m'' = normalize_nauty m';

val m = paley_graph 9;




load "graph";

val m = paley_graph 13;


fun g p =
  let
    fun f k (a,b) = is_square_mod (((a - b) - k) mod p, p);
    val shiftl = List.tabulate (p,I);
    val fl = map f shiftl;
    val fl' = map (fn x => (p,x)) fl;
    val rl = map max_clique_both0 fl'
  in
    rl
  end;


(* vertex degrees in the neighbor graph *)
fun f p (a,b) = is_square_mod ((a - b) mod p, p);

val p = 17

fun degree2 p = 
  let
    val g = f p;
    val vl = List.tabulate (p,I)
    val neighborl = filter (fn x => g(0,x)) (tl vl)
    val v0 = hd neighborl
    val neighborl2 = filter (fn x => g(v0,x)) (tl neighborl)
    
    fun degree vl a = 
      let fun f x = if a = x then false else g(a,x) in
        length (filter f vl)
      end;
  in
    map_assoc (degree neighborl2) neighborl2
  end;
  
val l = filter (fn x => x mod 4 = 1) (primes_leq 128);
val r = map degree2 l;

fun is_constant l = case l of 
    [] => true
  | [b] => true
  | a :: b :: m => b = a andalso is_constant (b :: m);  

all (is_constant o map snd) r;

x - a  - b


val rll = map g l;
fun test l = all (fn x => (hd l) < x-2) (tl l);
map test rll;






val fl = map_assoc f l;
val scl = map (fn (a,b) => (a,eval (a,b))) fl;
fun dominate (a,b) (c,d) = b <= d;
fun remove_worse a l = filter (fn x => not (dominate a x)) l;
fun loop l = case l of [] => [] 
             | a :: m => 
  let val l' = remove_worse a m in a :: loop l' end;

val bestl = (rev o loop o rev) scl;

(a-b)=(b-a)

which Paley graphs are subgraphs of each other?


val sclorg = [(2, 2), (3, 2), (5, 2), (7, 3), (11, 4), (13, 3), (17, 3), (19, 4),
    (23, 5), (29, 4), (31, 5), (37, 4), (41, 5), (43, 6), (47, 6), (53, 5),
    (59, 7), (61, 5), (67, 7), (71, 7), (73, 5), (79, 7), (83, 7), (89, 5),
    (97, 6), (101, 5), (103, 9), (107, 8), (109, 6), (113, 7), (127, 9),
    (131, 9), (137, 7), (139, 8), (149, 7), (151, 9), (157, 7), (163, 10),
    (167, 9), (173, 8), (179, 10), (181, 7), (191, 9), (193, 7), (197, 8),
    (199, 10), (211, 10), (223, 10), (227, 10), (229, 9), (233, 7),
    (239, 10), (241, 7), (251, 11)];
[(5, 2), (17, 3), (37, 4), (101, 5), 
 (109, 6), (281, 7), (373, 8)]

find other permutations?

[int_div 17 5, int_div 37 17, int_div 101 37, int_div 109 101, int_div 281 109];

val sclorg' = filter (fn (x,y) => x mod 4 = 1) sclorg
val scl' = filter (fn (x,y) => x mod 4 = 1) scl;

val bestl' = (rev o loop o rev) scl';

fun all_ssquares_mod b =
  if b = 0 
  then enew Int.compare [] 
  else enew Int.compare (map (fn x => ((x * x) + 2*x+1) mod b) (List.tabulate (b,I)));

val l1 = map_assoc (elength o all_ssquares_mod) l;

val vn = last (filter (fn x => x mod 4 = 1) (primes_leq 269)); 

int_div 37 5;
int_div 109 37;
int_div 241 109;

(* 
idea: look at growth rate of size of clique
need the maxclique algorithm 
*)

val f = create_f2 vn (vn+1);
val vl = List.tabulate (vn, fn x => x);
exist_clique 8 f vl;
exist_clique 8 (not o f) vl;
val l1 = all_clique 8 f vl;
val l2 = all_clique 8 (not o f) vl;

fun all_diff l = 
  let val r = cartesian_product l l in
    mk_fast_set Int.compare (map (fn (a,b) => (a-b) mod vn) r)
  end;

val l1' = mk_fast_set (list_compare Int.compare) (map all_diff l1);



val cliquesize = 6
val vn = int_pow 2 cliquesize;
val f = create_f vn;
val vl = filter (fn x => x mod 4 = 1) (primes_leq vn); 
length vl;
val l1 = all_clique 3 f vl;
val l2 = all_clique 3 (not o f) vl;



exist_clique (cliquesize+2) f vl;
exist_clique (cliquesize+1) (not o f) vl;


val vl = (List.tabulate (vn-2, fn x => x + 2));
val vl = primes_leq vn;
*)


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
mkdir ramsey22extra
cp ramsey22/hist/itsol11 ramsey22extra/input
cd ..
sh hol.sh
load "ramsey"; open ramsey;
parallel_exec "ramsey22extra";
*)

(*
Stirling number
*)

(*
load "aiLib"; open aiLib;
load "ramsey"; open ramsey;

val tot = 1024;

local open IntInf in
fun g(x) = (3 * x) div 2;
fun f n acc =  
  if n <= 1 then rev acc else f (n-1) (g (hd acc) :: acc);
end;

val ll = List.tabulate (tot, 
  fn x => f (IntInf.fromInt tot) [IntInf.fromInt x]);

local open IntInf in
val rr = map (map (fn x => x mod 2)) ll;
end;

val vv = Vector.fromList (map Vector.fromList rr);

fun f(a,b) = Vector.sub (Vector.sub (vv,a),b);
fun f'(a,b) = if a <= b 
  then f(a,b) > IntInf.fromInt 0 else f(b,a) > IntInf.fromInt 0;

val (r,t) = add_time max_clique_both (tot,f');

writel (selfdir ^ "/collatz_ramsey1024) [its r];

8, 4
16, 5
32, 8
64, 9
128, 11
256, 13
512, 14
1024, 
*)

(* -------------------------------------------------------------------------
   Ranking programs according to their scores
   ------------------------------------------------------------------------- *)

fun timed_prog3 p = 
  let
    val _ = push_counter := 0
    val f0 = exec_memo.mk_exec p
    fun f1 n i j = 
      (
      exec_memo.n_glob := IntInf.fromInt n;
      abstimer := 0; timelimit := !timeincr;
      hd (f0 (convert i, convert j))
      )
  in
    f1
  end

val bl_glob = ref ([]: bool list)

fun mk_cache2 f = 
  let 
    val d = ref (dempty (cpl_compare Int.compare Int.compare)) 
    fun g k =
        (
        case dfindo k (!d) of 
          SOME v => v  
        | NONE => let val v = f k in 
            (bl_glob := v :: !bl_glob; d := dadd k v (!d); v) end
        )
  in
    g                   
  end   
  
  
fun not_exist_clique_both tim k f =
  let val vl = List.tabulate (int_pow 2 k, I) in
    if exist_clique_timer tim (2*k) f vl then false
    else if exist_clique_timer tim (2*k) (not o f) vl then false
    else true     
  end
 
fun ramsey_score_nicer f k =
  let
    fun f1 (a,b) = if a=b then false else (if a < b then f(a,b) else f(b,a))
    val m = mat_tabulate (int_pow 2 k,f1)
    fun f2 (a,b) = mat_sub (m,a,b)
  in
    if not_exist_clique_both 10000000 k f2
    then (if k >= 6 
          then (k, hash_bl (!bl_glob)) 
          else ramsey_score_nicer f (k+1))
    else (k-1, hash_bl (!bl_glob))
  end
  
fun ramsey_score p = 
  if !rams_nicer then 
    let 
      val _ = bl_glob := []
      val f = mk_cache2 (timed_prog p) 
    in
      SOME (ramsey_score_nicer f 2) handle  
        Empty => NONE
      | Div => NONE
      | ProgTimeout => NONE
      | Overflow => NONE
      | RamseyTimeout => NONE 
    end 
  else if !rams_dnf then 
    let 
      val f = timed_prog3 p 
      val bl = ref []
      val r = loop_pass_clausel bl f (3,7,100000000)
    in
      if r <= 2 then NONE else SOME (r,hash_bl (!bl))
    end
  else
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


end (* struct *)   



