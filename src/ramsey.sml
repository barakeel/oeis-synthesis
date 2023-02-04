structure ramsey :> ramsey =
struct

open HolKernel Abbrev boolLib aiLib kernel smlParallel
val ERR = mk_HOL_ERR "ramsey"

(* -------------------------------------------------------------------------
   Takes the basic array: put the last vertex at index n-1 to index 0
   and index 0 to n-2 maps to 1 to n-1.
   ------------------------------------------------------------------------- *)

fun mk_sym a gsize = 
  let fun f (x,y) = if x = y then false else 
                    if x < y then Array2.sub (a,x,y)
                    else Array2.sub (a,y,x) 
  in
    Array2.tabulate Array2.RowMajor (gsize,gsize,f)
  end

fun invert a gsize =
  let fun f (x,y) = if x = y then false else not (Array2.sub (a,x,y)) in
    Array2.tabulate Array2.RowMajor (gsize,gsize,f)
  end
  
(* sigma is a permutation from new indices to old indices *)
fun permute sigma a gsize =
  let fun f (x,y) = Array2.sub (a,sigma x,sigma y) in
    Array2.tabulate Array2.RowMajor (gsize,gsize,f)
  end

(* permute so that the new vertex have index 0 *)
fun cycle a gsize =
  let fun sigma x = if x = 0 then gsize-1 else x-1 in
    permute sigma a gsize
  end

fun cut a gsize = 
  let fun f (x,y) = Array2.sub (a,y,x) in
    Array2.tabulate Array2.RowMajor (gsize,gsize,f)
  end


(* -------------------------------------------------------------------------
   All cliques containing a list of set of vertices
   ------------------------------------------------------------------------- *)

fun has_edge a x y = Array2.sub (a,x,y)

fun apprange f (minv,maxv) =
  let fun loop x = if x <= maxv then (f x; loop (x+1)) else () in 
    loop minv 
  end
  
fun update_clique a gsize l (clique,startn) =
  let fun f x = 
    if all (has_edge a x) clique 
    then l := (x :: clique, x + 1) :: !l 
    else ()
  in
    apprange f (startn, gsize - 1)
  end

fun all_clique a gsize extran cliquel = 
  let fun next_cliquel cliquel =
    let val l = ref [] in (app (update_clique a gsize l) cliquel; !l) end
  in
    funpow extran next_cliquel cliquel
  end

(* -------------------------------------------------------------------------
   All cliques containing the last vertex
   ------------------------------------------------------------------------- *)
  
fun contains_clique a gsize size1 size2 = 
  let 
    val aanti = invert a gsize
    val cliquel = all_clique a gsize (size1 - 1) [([gsize - 1],0)]
    val anticliquel = all_clique aanti gsize (size2 - 1) [([gsize - 1],0)]
  in
    not (null cliquel) orelse not (null anticliquel)
  end

(* -------------------------------------------------------------------------
   All cliques containing two vertices
   ------------------------------------------------------------------------- *)

fun update_array a f gsize = 
  let 
    fun loop i = 
      if i >= gsize - 1 then () else
      let val b = f (i,gsize-1) in
        Array2.update (a,i,gsize-1,b);
        Array2.update (a,gsize-1,i,b);
        loop (i+1)
      end   
  in
    (loop 0; true)
  end
  handle Div => false | ProgTimeout => false | Overflow => false

fun ramsey f n size1 size2 = 
  let
    val a = Array2.tabulate Array2.RowMajor (n,n,fn _ => false)  
    fun loop gsize = 
      if gsize > n then (a, gsize-1) else
      (
      if not (update_array a f gsize) then (a, gsize-1) 
      else if contains_clique a gsize size1 size2 
        then (a, gsize-1) 
      else loop (gsize + 1)
      )
  in
    loop 1
  end
  
(* -------------------------------------------------------------------------
   Search procedure using a predicate as a filter 
   (true = continue introduce 1 and ~1 in the array, false = stop)
   ------------------------------------------------------------------------- *) 

(*
val maxsize = 40;
fun ramsey_search_one maxwidth maxtime graph (x,y) =
  let val _ = initialize array2 with_ graph in
    if f (x,y) > 0 then () else
    rl := v2_update (graph1,x,y,1) :: 
          v2_update (graph2,x,y,~1) :: (!rl)
  end


fun ramsey_search f maxsize maxwidth maxtime =
  let
    
  in
  *)  
  
 (* -------------------------------------------------------------------------
   Matrix operations
   ------------------------------------------------------------------------- *) 
  
fun mat_sub (m,i,j) = Vector.sub (Vector.sub (m,i),j)
  
fun mat_update (m,i,j,v) =
  Vector.update (m,i, Vector.update (Vector.sub (m,i),j,v))

fun mat_update_sym (m,i,j,v) =
  mat_update (mat_update (m,i,j,v),j,i,v)

fun grow_matrix v = 
  let 
    val size = Vector.length v
    val newline = Vector.tabulate (size + 1, fn _ => false)
    val newcol = Vector.fromList [false]
    fun f x = Vector.concat [x,newcol]
  in
    Vector.concat [Vector.map f v, Vector.fromList [newline]]
  end  
  
(* -------------------------------------------------------------------------
   All cliques containing a list of set of vertices
   ------------------------------------------------------------------------- *)

type board = bool vector vector * bool vector vector * int

fun mhas_edge m x y = mat_sub (m,x,y)
  
fun mupdate_clique m l (clique,startn) =
  let fun f x = 
    if all (mhas_edge m x) clique 
    then l := (x :: clique, x + 1) :: !l 
    else ()
  in
    apprange f (startn, Vector.length m - 1)
  end

fun mall_clique m extran cliquel = 
  let fun next_cliquel cliquel =
    let val l = ref [] in (app (mupdate_clique m l) cliquel; !l) end
  in
    funpow extran next_cliquel cliquel
  end
  
(* -------------------------------------------------------------------------
   Basic MCTS
   ------------------------------------------------------------------------- *)

val pairl = List.concat (List.tabulate (41, 
      fn x => (List.tabulate (x, fn y => (x,y)))));
val pairv = Vector.fromList pairl


val edge_proba = ref 0.5
fun random_move () = random_real () < (!edge_proba)


val starting_board = 
  (
  Vector.fromList [Vector.fromList [false]],
  Vector.fromList [Vector.fromList [false]],
  0
  )

val color1 = 4
val color2 = 6

fun is_valid (graph,antigraph,i) =    
  if i = 0 then true else 
  let 
    val (a1,a2) = Vector.sub (pairv,i-1)
    val move = mat_sub (graph,a1,a2)
    val cliquel =
      if move
      then mall_clique graph (color1 - 2) [([a1,a2],0)]
      else mall_clique antigraph (color2 - 2) [([a1,a2],0)]   
  in
    null cliquel
  end
   
fun apply_move (graph,antigraph,i) move =
  let 
    val (a1,a2) = Vector.sub (pairv,i)
    val (graph',antigraph') = 
      if a1 >= Vector.length graph 
      then (grow_matrix graph, grow_matrix antigraph)
      else (graph, antigraph)
    val (graph'',antigraph'') = (mat_update_sym (graph',a1,a2,move),
      mat_update_sym (antigraph',a1,a2, not move))
    val newstate = (graph'',antigraph'',i+1) 
  in
    if is_valid newstate then SOME (graph'',antigraph'',i+1) else NONE
  end

fun score_board board =
  if #3 board <= 0 then 0.0 else 
  let val (a,b) = Vector.sub (pairv, #3 board - 1) in
    Real.fromInt a + int_div b a
  end

fun simul_once board =
  case apply_move board (random_move ()) of
    SOME newboard => simul_once newboard
  | NONE => score_board board

val bestscore = ref 0.0

fun simul n board =
  let 
    fun f i = simul_once board 
    val l1 = List.tabulate (n*n,f)
    val l2 = rev (dict_sort Real.compare l1)
    val l10 = first_n n l2
    val sc = average_real l10
  in
    if hd l10 > !bestscore then bestscore := hd l10 else ();
    sc
  end

(*
load "ramsey"; open aiLib ramsey;

edge_proba := 0.5;
val r = time (simul 100000) starting_board;
fun f x = (edge_proba := int_div x 10; simul 10000 starting_board); 
val l1 = List.tabulate (10,f);
val l2 = number_fst 0 l1;
val l3 = rev (dict_sort (snd_compare (list_compare Real.compare)) l2);

fun f x = (edge_proba := 0.32 + int_div x 100; simul 100000 starting_board); 
val l1 = List.tabulate (4,f);
val l2 = number_fst 0 l1;
val l3 = rev (dict_sort (snd_compare (list_compare Real.compare)) l2);
best is 34 percent. best score = 19

big steps sampled according to the number of visits
*)

(* -------------------------------------------------------------------------
   Simple Monte Carlo Tree Search (score = depth)
   ------------------------------------------------------------------------- *) 

val explo = ref 1.0
val moven = 2
val nsimul = ref 40
val movev = Vector.fromList [false,true]


type move = bool
datatype mtree = 
  MNode of board * real ref * real ref  * mtree option ref vector

val parentref = ref []

fun empty_cv () = Vector.tabulate (moven, fn _ => ref NONE)
  
fun init_tree () = 
  MNode (starting_board, ref (simul (!nsimul) starting_board), 
  ref 1.0, empty_cv ())

fun ucb vispar co = case (!co) of 
    NONE => 1000000.0 + random_real ()
  | SOME (MNode (_,sum,vis,_)) => 
     !sum / !vis + !explo * Math.sqrt (Math.ln vispar / !vis)
     
      (*  !sum / !vis + !explo * (Math.sqrt vispar / !vis) *)

fun select (mtree as (MNode (_,sum,vis,cv))) =
  let 
    val _ = parentref := (sum,vis) :: !parentref
    val ci = vector_maxi (ucb (!vis)) cv
  in
    case !(Vector.sub (cv,ci)) of 
      NONE => (mtree,ci)
    | SOME newmtree => select newmtree
  end
  
fun update_cv state cv sc ci =
  let val r = Vector.sub (cv,ci) in 
    r := SOME (MNode (state , ref sc, ref 1.0, empty_cv ()))
  end
    
fun update_parent sc (sum,vis) = (sum := !sum + sc; vis := !vis + 1.0)
    
fun expand (mtree as MNode (state,sum,vis,cv), ci) = 
  case apply_move state (Vector.sub (movev,ci))  of
    NONE => app (update_parent (!sum / !vis)) (!parentref)
  | SOME newstate =>
    let val sc = simul (!nsimul) newstate in
      update_cv newstate cv sc ci;
      app (update_parent sc) (!parentref) 
    end

fun mcts_once mtree =
  let 
    val _ = parentref := []
    val (mnode,ci) = select mtree 
  in 
    expand (mnode,ci)
  end
   
fun mcts mtree nsim = 
  if nsim <= 0 
  then mtree 
  else (mcts_once mtree; mcts mtree (nsim - 1))   
 
(* -------------------------------------------------------------------------
   Big steps
   ------------------------------------------------------------------------- *) 

fun vis_of co = case (!co) of 
    NONE => 0.0
  | SOME (MNode (_,sum,vis,_)) => !vis;

fun select_maxvis mtree = case mtree of MNode (_,r1,r2,cv) => 
  let 
    val dis = number_fst 0 (map vis_of (vector_to_list cv))
    val ci = select_in_distrib dis 
  in
    print_endline (pretty_real (!r1 / !r2) ^ ": " ^ 
      bts (Vector.sub (movev,ci)) ^ " " ^
      pretty_real (!bestscore)
      );
    (!(Vector.sub (cv,ci)))
  end
 
fun bigsteps nsim mtree = 
  case select_maxvis (mcts mtree nsim) of
    NONE => print_endline "end bigsteps"
  | SOME newtree => bigsteps nsim newtree


fun bigsteps_fun () = 
  let 
    fun f () = (nsimul := 1; bestscore := 0.0; bigsteps 1000000 (init_tree ()))
    val (_,t) = add_time f () 
  in
    print_endline ("bigstep time: " ^ rts_round 2 t)
  end
  
val ramseyspec : (unit, unit, unit) extspec =
  {
  self_dir = selfdir,
  self = "ramsey.ramseyspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = let fun f () () = bigsteps_fun () in f end,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = let fun f file arg = () in f end,
  read_arg = let fun f file = () in f end,
  write_result = let fun f file arg = () in f end,
  read_result = let fun f file = () in f end
  }
  
fun bigsteps_parallel expname ncore = 
  let 
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = smlExecScripts.buildheap_dir := dir
    val _ = mkDir_err dir
    val _ = smlExecScripts.buildheap_options := 
      "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) 
         handle NotFound => 8000) 
    val l = List.tabulate (32 * 8, fn _ => ())
  in
    smlParallel.parmap_queue_extern ncore ramseyspec () l
  end
  
(*
load "ramsey"; open ramsey;
load "aiLib"; open aiLib;
bigsteps_parallel "ramseypar" 32;
*)
  
  
(* -------------------------------------------------------------------------
   Graph normalization
   ------------------------------------------------------------------------- *)

fun more_edge a gsize =
  let 
    val edgel = 
      List.tabulate (gsize - 1, fn x => List.tabulate (x, fn y => (x,y)))  
    fun f (x,y) =
      if Array2.sub (a,x,y) then () else
        (
        Array2.update (a,x,y,true);
        Array2.update (a,y,x,true);
        if null (all_clique a gsize (4 - 2) [([x,y],0)])
        then () 
        else 
          (Array2.update (a,x,y,false);
           Array2.update (a,y,x,false))
        )      
  in
    app f (List.concat edgel)
  end

fun neighbor_of a gsize x = 
  let 
    val l = ref []
    fun loop y = 
      if y >= gsize then ()
      else (if Array2.sub (a,x,y) orelse x = y 
            then l := y :: !l else (); 
            loop (y + 1))
  in
    loop 0; 
    mk_fast_set Int.compare (!l)
  end
  
fun all_neighbor a gsize =
  Vector.tabulate (gsize, fn x => neighbor_of a gsize x)

fun charac nv a gsize x =
  let
    val l = ref []
    fun loop nl = 
      let 
        val nll = map (fn y => Vector.sub (nv,y)) nl
        val newnl = mk_fast_set Int.compare (List.concat nll) 
      in
        if newnl = nl then () else
        (l := length newnl :: !l; loop newnl)
      end
  in
    loop [x]; rev (!l)
  end
    
fun all_charac a gsize =
  let val nv = all_neighbor a gsize in
    List.tabulate (gsize, fn x => (x, charac nv a gsize x))   
  end

fun norm_graph a gsize =
  let
    val _ = more_edge a gsize
    val cl = all_charac a gsize
    val clsorted = dict_sort (snd_compare (list_compare Int.compare)) cl
    val cv = Vector.fromList (map fst clsorted)
    fun sigma x = Vector.sub (cv,x)
  in
    permute sigma a gsize
  end

end (* struct *)

(* -------------------------------------------------------------------------
   Test
   ------------------------------------------------------------------------- *)

(*
load "ramsey"; open ramsey;
load "aiLib"; open aiLib;
fun frandom (a,b) = random_real () < 0.5;
fun fglob () = ramsey frandom 50 4 6;
fun f () = hd (dict_sort compare_imax  (List.tabulate (100000,fn _ => fglob ())));
val (abest,nbest) = time f ();

load "ramsey"; open ramsey;
load "aiLib"; open aiLib;
val tree = init_tree ();
PolyML.print_depth 2;
val newtree = time (mcts tree) 1000;
!bestscore;




*)

(*
load "ramsey"; open ramsey;
load "aiLib"; open aiLib;
val gsize = 8;
val a = Array2.tabulate Array2.RowMajor 
  (gsize,gsize,fn _ => random_real () < 0.5);
val asym = mk_sym a gsize;

val cliquel = all_clique asym gsize 5;

val charac = all_charac asym gsize;
val anorm = norm_graph asym gsize;
val characnorm = all_charac anorm gsize;

*)
