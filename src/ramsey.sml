structure ramsey :> ramsey =
struct

open HolKernel Abbrev boolLib aiLib kernel smlParallel
val ERR = mk_HOL_ERR "ramsey"
type mat = bool vector vector
type graph = mat * mat * int
datatype branch = Follow | Avoid | Backtrack

(* -------------------------------------------------------------------------
   Global parameters
   ------------------------------------------------------------------------- *) 

val color1 = 4
val color2 = 6

(* -------------------------------------------------------------------------
   Matrix operations
   ------------------------------------------------------------------------- *) 
 
fun apprange f (minv,maxv) =
  let fun loop x = if x <= maxv then (f x; loop (x+1)) else () in 
    loop minv 
  end 

fun mat_sub (m,i,j) = Vector.sub (Vector.sub (m,i),j)
  
fun mat_update (m,i,j,v) =
  Vector.update (m,i, Vector.update (Vector.sub (m,i),j,v))

fun mat_update_sym (m,i,j,v) =
  mat_update (mat_update (m,i,j,v),j,i,v)

fun mat_tabulate (n,f) = 
  Vector.tabulate (n,fn x => Vector.tabulate (n, fn y => f (x,y)))

fun mat_enlarge m size = 
  let
    val oldsize = Vector.length m
    fun f (x,y) = if x >= oldsize orelse y >= oldsize 
                  then false
                  else mat_sub (m,x,y)
  in
    mat_tabulate (size,f)
  end
  
fun mat_crop m size = 
  let
    val oldsize = Vector.length m
    fun f (x,y) = mat_sub (m,x,y)
  in
    mat_tabulate (size,f)
  end
  
fun mat_resize m size = 
  if size = Vector.length m then m 
  else if size > Vector.length m then mat_enlarge m size   
  else mat_crop m size

fun mat_permute m sigma =
  let fun f (x,y) = mat_sub (m, sigma x, sigma y) in
    mat_tabulate (Vector.length m, f)
  end

(* -------------------------------------------------------------------------
   Graph operations
   ------------------------------------------------------------------------- *)
  
val edgel = List.concat (List.tabulate (41, 
      fn x => (List.tabulate (x, fn y => (x,y)))));
val edgev = Vector.fromList edgel  
  
val starting_graph = 
  (
  Vector.fromList [Vector.fromList [false]],
  Vector.fromList [Vector.fromList [false]],
  0 (* index of the next edge in the edgev *)
  )  

fun has_edge m x y = mat_sub (m,x,y)
  
fun graph_add (mt0,mf0,i) b = 
  let 
    val (a1,a2) = Vector.sub (edgev,i)
    val (mt1,mf1) = (mat_resize mt0 (a1+1), mat_resize mf0 (a1+1))
    val (mt2,mf2) = (mat_update_sym (mt1,a1,a2,b),
                     mat_update_sym (mf1,a1,a2,not b))
  in
    (mt2,mf2,i+1)
  end

(* -------------------------------------------------------------------------
   Compute cliques in one graph
   ------------------------------------------------------------------------- *)

fun update_clique m l (clique,i) =
  let
    fun f x =
      if all (has_edge m x) clique
      then l := (x :: clique, x+1) :: !l 
      else ()
  in
    apprange f (i, Vector.length m - 1)
  end

fun all_clique m n cliquel = 
  let 
    fun next_cliquel cliquel =
      let val l = ref [] in (app (update_clique m l) cliquel; !l) end
  in
    funpow n next_cliquel cliquel
  end  

(* -------------------------------------------------------------------------
   Graph normalization
   ------------------------------------------------------------------------- *)

fun more_edge mt i =
  let  
    fun f ((x,y),m) =
      if mat_sub (m,x,y) then m else
        (
        let val newm = mat_update_sym (m,x,y,true) in
          if null (all_clique newm (color1 - 2) [([x,y],0)])
          then newm
          else m
        end
        )  
  in
    foldl f mt (first_n i edgel)  
  end

fun neighbor_of m x = 
  let fun test y = mat_sub (m,x,y) in
    filter test (List.tabulate (Vector.length m, I))
  end
  
fun all_neighbor m = 
  Vector.tabulate (Vector.length m, neighbor_of m)

fun charac nv x =
  let
    val l = ref []
    fun loop nl = 
      let 
        val nll = map (fn y => Vector.sub (nv,y)) nl
        val newnl = mk_fast_set Int.compare (List.concat nll) 
      in
        if newnl = nl then () else (l := length newnl :: !l; loop newnl)
      end
  in
    loop [x]; rev (!l)
  end
    
fun all_charac m =
  let val nv = all_neighbor m in
    List.tabulate (Vector.length m, fn x => (x, charac nv x))   
  end

fun norm_graph (mt0,mf0,i) =
  let
    (* val newm = more_edge mt0 i *)
    val cl = all_charac mt0
    val clsorted = dict_sort (snd_compare (list_compare Int.compare)) cl
    val cv = Vector.fromList (map fst clsorted)
    fun sigma x = Vector.sub (cv,x)
  in
    (mat_permute mt0 sigma, i)
  end

(* -------------------------------------------------------------------------
   Backtracking
   ------------------------------------------------------------------------- *)


val bcache = Vector.tabulate (Vector.length edgev, fn _ => ref NONE)
fun clean_bcache () = Vector.app (fn x => x := NONE) bcache
val ncall = ref 0
val bestgraph = ref starting_graph

fun ramsey_init () = (clean_bcache (); bestgraph := starting_graph; ncall := 0)

fun new_branch (mt,mf,i) =
  let 
    val (a1,a2) = Vector.sub (edgev,i-1)
    val borg = valOf (!(Vector.sub (bcache,i-1)))
  in
    if borg = mat_sub (mt,a1,a2) then Avoid else Backtrack
  end
  
(* could downsize one step quicker *)
fun graph_remove (mt0,mf0,i) =
  let 
    val (a1,a2) = Vector.sub (edgev,i-1)
    val (mt1,mf1) = (mat_resize mt0 (a1+1), mat_resize mf0 (a1+1))
    val (mt2,mf2) = (mat_update_sym (mt1,a1,a2,false),
                     mat_update_sym (mf1,a1,a2,false))
  in
    (mt2,mf2,i-1)
  end

fun mat_to_list (m,i) = map (fn (a,b) => mat_sub (m,a,b)) (first_n i edgel)

fun better_graph (mt1,mf1,i1) (mt2,mf2,i2) =
  if i1 > i2 
    then true else
  if i1 = i2 
    then list_compare bool_compare 
      (mat_to_list (mt1,i1), mat_to_list (mt2,i2)) = LESS
  else false

(* -------------------------------------------------------------------------
   Compute the largest ramsey graph
   ------------------------------------------------------------------------- *)

(* for backtracking *)
fun ramsey_loop f (graph as (mt0,mf0,i0)) branch = 
  if !ncall > ((i0+1) * (i0+1) div 100) + 10 then !bestgraph else
  let 
    val (a1,a2) = Vector.sub (edgev,i0)
    val bo = 
      let val boref = (Vector.sub (bcache,i0)) in
        case !boref of SOME x => SOME x | NONE => 
          let val r = SOME (f (a1,a2)) 
            handle Div => NONE | ProgTimeout => NONE | Overflow => NONE
          in
            boref := r; r
          end
      end  
  in
    case bo of NONE => !bestgraph | SOME borg => 
      (
      case branch of 
        Backtrack => 
          if i0 <= 0 then raise ERR "ramsey_loop" "saturated" else
            ramsey_loop f (graph_remove graph) (new_branch graph)
      | _ =>      
      let
          (* val _ = print_endline 
          (its i0 ^ ": " ^ its a1 ^ "-" ^ its a2 ^ ", " ^ bts b) *)
        val _ = incr ncall
        val b = case branch of 
            Follow => borg
          | Avoid => not borg
          | Backtrack => raise ERR "" "should not happen"      
        val (newgraph as (mt1,mf1,i1)) = graph_add graph b
        val _ = if better_graph newgraph (!bestgraph) 
                then bestgraph := newgraph
                else ()
        val m = if b then mt1 else mf1
        val color = if b then color1 else color2
      in
        case branch of 
           Follow =>
           if null (all_clique m (color - 2) [([a1,a2],0)])
           then ramsey_loop f newgraph Follow
           else ramsey_loop f graph Avoid
         | Avoid =>
           if null (all_clique m (color - 2) [([a1,a2],0)])
           then ramsey_loop f newgraph Follow
           else ramsey_loop f graph Backtrack
         | Backtrack => raise ERR "" "should not happen"
      end
      )
  end
  
fun ramsey f = (ramsey_init (); ramsey_loop f starting_graph Follow)

  
(* -------------------------------------------------------------------------
   Test
   ------------------------------------------------------------------------- *)

(*
load "ramsey"; open ramsey;
load "aiLib"; open aiLib;
fun frandom (a,b) = random_real () < 0.5;
fun f () = ramsey frandom;
val _ = time List.tabulate (1000,fn _ => f ());

PolyML.print_depth 2;
val r = time ramsey frandom;
*)


  
  
(* 4 matrices original values + changed values 
   (both anti and for) 
 *)

(* This was MCTS
(* -------------------------------------------------------------------------
   All cliques containing a list of set of vertices
   ------------------------------------------------------------------------- *)

type board = bool vector vector * bool vector vector * int


  
(* -------------------------------------------------------------------------
   Basic MCTS
   ------------------------------------------------------------------------- *)




val edge_proba = ref 0.5
fun random_move () = random_real () < (!edge_proba)


val starting_board = 
  (
  Vector.fromList [Vector.fromList [false]],
  Vector.fromList [Vector.fromList [false]],
  0
  )



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
*)
  


end (* struct *)


