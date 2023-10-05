structure sat :> sat =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty rconfig
val ERR = mk_HOL_ERR "sat"


(* flags conspiring to output all models *)
val allsat_flag = ref false
val degree_flag = ref false
val max_blue_degree = ref 0
val max_red_degree = ref 0
val iso_flag = ref true
val graphl = ref []

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val edgel_glob = ref []
val edgel_n = ref 0
val blue_size_glob = ref 0
val red_size_glob = ref 0
val limit_glob = 
  (if abstract_time > 0 then SOME abstract_time else NONE, 
   if real_time > 0.0 then SOME (Time.fromReal real_time) else NONE)
val timer = ref (Timer.startRealTimer ())
val isod_glob = ref (eempty IntInf.compare)

(* -------------------------------------------------------------------------
   Timer and statistics
   ------------------------------------------------------------------------- *)

exception RamseyTimeout;

val prop_timer = ref 0.0
val iso_timer = ref 0.0
val iso_timer2 = ref 0.0
val prop_counter = ref 0
val prop_small_counter = ref 0
val prop_conflict_counter = ref 0
val iso_counter = ref 0
val norm_failure = ref 0
val degree_counter = ref 0
val degree_timer = ref 0.0
val degree_conflict_counter = ref 0

val other_counter = ref 0
val other_timer = ref 0.0

fun init_timer () =
  (
  graphl := [];
  prop_counter := 0;
  prop_small_counter := 0;
  prop_conflict_counter := 0;
  prop_timer := 0.0;
  iso_counter := 0;
  iso_timer := 0.0;
  iso_timer2 := 0.0;
  norm_failure := 0;
  other_counter := 0;
  other_timer := 0.0;
  degree_counter := 0;
  degree_conflict_counter := 0;
  degree_timer := 0.0; 
  timer := Timer.startRealTimer ()
  )

fun test_timer () =
  let
    val _ = incr prop_counter
    val _ = if !prop_counter mod 1000 = 0 then print "." else ()
    val _ = case fst (limit_glob) of NONE => () | SOME ti => 
      if !prop_counter > ti then raise RamseyTimeout else ()
    val _ = case snd (limit_glob) of NONE => () | SOME tr => 
      if Timer.checkRealTimer (!timer) > tr then raise RamseyTimeout else ()
  in
    ()
  end

fun stats () = 
  (  
  if null (!graphl) then log "unsat" 
    else log ("sat " ^ its (length (!graphl)));
  log ("prop: " ^ its (!prop_counter) ^ " calls, " ^ 
                  its (!prop_small_counter) ^ " propagations, " ^ 
                  its (!prop_conflict_counter) ^ " conflicts, " ^ 
                  rts_round 6 (!prop_timer) ^ " seconds");
  log ("iso: " ^ its (!iso_counter) ^ " calls, " ^ 
       its ((!iso_counter) - (elength (!isod_glob))) ^ " conflicts, " ^
       rts_round 6 (!iso_timer) ^ " seconds, " ^
       rts_round 6 (!iso_timer2) ^ " seconds"
       );
  log ("degree: " ^ its (!degree_counter) ^ " calls, " ^ 
                    its (!degree_conflict_counter) ^ " conflicts, " ^ 
                    rts_round 6 (!degree_timer) ^ " seconds");       
  log ("other: " ^ its (!other_counter) ^ " calls");    
  if !norm_failure > 0 then log ("norm: " ^ its (!norm_failure)) else ();
  !graphl
  )

(* -------------------------------------------------------------------------
   Order in which the vertices should be colored
   ------------------------------------------------------------------------- *)

fun pairbelowy y = List.tabulate (y,fn x => (x,y))

fun search_order_undirected size = 
  List.concat (List.tabulate (size,fn y => pairbelowy y))

fun search_order size = List.concat 
  (map (fn (x,y) => [(x,y),(y,x)]) (search_order_undirected size))

fun search_order_linear size = 
  filter (fn (x,y) => x <> y)
  (cartesian_product (List.tabulate (size,I)) (List.tabulate (size,I)))

fun search_order_linear_undirected size = 
  filter (fn (x,y) => x < y)
  (cartesian_product (List.tabulate (size,I)) (List.tabulate (size,I)))

(* -------------------------------------------------------------------------
   Test isomorphism
   ------------------------------------------------------------------------- *)
    
fun is_iso_aux graph =
  let 
    (* val _ = debugf "graph: " string_of_graph graph *)
    val normgraph = normalize_nauty graph
    (* val _ = debugf "normgraph: " string_of_graph normgraph *)
    val graphid = zip_mat normgraph
    (* val _ = debugf "graphid: " IntInf.toString graphid *)
  in
    if emem graphid (!isod_glob)   
    then true
    else (isod_glob := eadd graphid (!isod_glob); false)
  end
  
fun is_iso graph =
  (incr iso_counter; total_time iso_timer is_iso_aux graph)

(* -------------------------------------------------------------------------
   Doubly-linked vector
   ------------------------------------------------------------------------- *)

(* returns a fucntion to undo the operation *)
fun dlv_del i dlv = 
  let 
    val ((predi,suci),_) = Vector.sub (dlv,i)
    val ((_,predf),_) = Vector.sub (dlv,!predi)
    (* val _ = debug ("2: " ^ its (!predi) ^ " " ^ its (!suci)) *)
    val ((sucb,_),_) = Vector.sub (dlv,!suci)
  in
    predf := !suci; sucb := !predi;
    fn () => (predf := i; sucb := i)
  end

fun dlv_fromlist dummy l = 
  let 
    val l1 = dummy :: (l @ [dummy])
    fun f i x = ((ref (i-1), ref (i+1)), x)
    val l2 = mapi f l1
  in
    Vector.fromList l2
  end
  
fun dlv_app f dlv = 
  let
    val last_index = Vector.length dlv - 1
    val first_index = (! o snd o fst) (Vector.sub (dlv,0)) 
    fun dlv_loop g start =
      if start = last_index then () else
      let 
        val ((_,nextref),x) = Vector.sub (dlv,start)
        val next = !nextref
      in
        g x; dlv_loop g next
      end
  in
    dlv_loop f first_index
  end

fun dlv_null dlv = 
  let 
    val last_index = Vector.length dlv - 1
    val first_index = (! o snd o fst) (Vector.sub (dlv,0)) 
  in
    first_index = last_index 
  end
  
(* -------------------------------------------------------------------------
   Conversion between edges and variables
   ------------------------------------------------------------------------- *)

val vartoedgev = Vector.fromList (search_order_undirected 50);

fun var_to_edge x = Vector.sub (vartoedgev,x) 
  handle Subscript => raise ERR "var_to_edge" ""

fun edge_to_var (x,y) = 
  if x < y then x + ((y * (y - 1)) div 2) else 
  raise ERR "edge_to_var" (its x ^ "-" ^ its y)

(* -------------------------------------------------------------------------
   Debug
   ------------------------------------------------------------------------- *)

fun cts c = 
  if c = 1 then "b" 
  else if c = 2 then "r"
  else if c = 0 then "w"
  else raise ERR "cts_color" (its c)

fun ets (edgeid,c) = 
  let val (a,b) = var_to_edge edgeid in
    its a ^ "-" ^ its b ^ ":" ^ cts c
  end
  
fun string_of_clausev clausev = 
  let fun f (bref,lit) = bts (!bref) ^ "@" ^ ets (fst (fst lit), snd lit) in
    String.concatWith " " (map f (vector_to_list clausev))
  end
  
fun string_of_assignv assignv = 
  let 
    val l1 = map (! o fst) (vector_to_list assignv)
    val l2 = number_fst 0 l1
  in
    String.concatWith " " (map ets l2)
  end  

(* -------------------------------------------------------------------------
   Ramsey clauses
   ------------------------------------------------------------------------- *)

fun subsets_of_size_faster n (l,ln) = 
  if n > ln then [] else if n = ln then [l] else
  (
  case l of
    [] => if n = 0 then [[]] else []
  | a :: m => 
    let
      val l1 = map (fn subset => a::subset) 
        (subsets_of_size_faster (n - 1) (m,ln-1))
      val l2 = subsets_of_size_faster n (m,ln-1)
    in
      l1 @ l2
    end  
  )

fun subsets_of_size n l =  subsets_of_size_faster n (l, length l)

fun clique_of_subset (subset,color) =
  let val edgel = all_pairs (dict_sort Int.compare subset) in
    map (fn x => (edge_to_var x, color)) edgel
  end

fun ramsey_clauses size (bluesize,redsize) = 
  let
    val bluesubsetl = subsets_of_size bluesize (List.tabulate (size,I))
    val redsubsetl = subsets_of_size redsize (List.tabulate (size,I))
    val subsetl = map_assoc (fn _ => blue) bluesubsetl @
                  map_assoc (fn _ => red) redsubsetl
  in
    map clique_of_subset subsetl
  end

(* -------------------------------------------------------------------------
   Move clauses into an efficient data structure for propagation
   ------------------------------------------------------------------------- *)

val graph_glob = ref (Array2.array (1,1,0));
val isograph_glob = ref (Array2.array (1,1,0));

(* 1 in the graph means blue, 
   1 in the sat problem means not blue *)

fun add_clause (clause,(assignv,clausevv)) =
  let
    val cid = Vector.length clausevv
    val nvar = Vector.length assignv
    val maxvar = list_imax (map fst clause)
    val newassignv = 
      if maxvar < nvar then assignv else
      let val v = 
        Vector.tabulate (maxvar + 1 - nvar, fn i => (ref [], ref []))
      in
        Vector.concat [assignv,v]
      end
    fun f cvid (vid,color) = 
      let 
        val (l1,l2) = Vector.sub (newassignv, vid) 
        val l = if color = blue then l1 else l2
        val vcid = length (!l) + 1
      in
        l := (cid,cvid) :: !l;
        ((vid,vcid),color)
      end
    val newclausev = Vector.fromList (mapi f clause)
    val newclausevv = Vector.concat [clausevv,Vector.fromList [newclausev]]
  in
    (newassignv, newclausevv)
  end
  
fun add_clausel clausel (assignv,clausevv) = 
  foldl add_clause (assignv,clausevv) clausel

fun transform_pb (assignv,clausevv) = 
  let 
    fun f1 (l1,l2) = (ref 0, 
      (dlv_fromlist (~1,~1) (rev (!l1)), dlv_fromlist (~1,~1) (rev (!l2))))
    fun f2 x = (Vector.map (fn y => (ref false, y)) x, ref 0)
  in
    (Vector.map f1 assignv, Vector.map f2 clausevv)
  end

fun init_sat size (bluesize,redsize) =
  let
    val _ = graph_glob := (Array2.array (size,size,0))
    val maxedge = (size * (size - 1)) div 2
    val assignv = Vector.tabulate (maxedge, (fn _ => (ref [], ref [])))
    val clausevv = Vector.fromList []
    val clausel = ramsey_clauses size (bluesize,redsize)
    val (newassignv,newclausevv) = add_clausel clausel (assignv,clausevv)
  in
    transform_pb (newassignv,newclausevv)
  end


(* -------------------------------------------------------------------------
   Propagation
   ------------------------------------------------------------------------- *)

exception Conflict;


fun propagated_clause clausev = 
  let fun loop i = 
    let val (bref,lit) = Vector.sub (clausev,i) in
      if not (!bref) then lit else loop (i+1)
    end
  in
    loop 0
  end
  handle Subscript => raise ERR "propagated_clause" (string_of_clausev clausev)


fun assign undol edgeid assignref color =
  let 
    val graph = !graph_glob
    val (a,b) = var_to_edge edgeid
    fun back () = (assignref := 0; mat_update_sym (graph,a,b,0))  
  in
    assignref := color;
    mat_update_sym (graph,a,b,color);
    undol := back :: !undol
  end


fun prop_sat_loop assignv clausevv queue undol = case !queue of 
    [] => (!undol, false)
  | (edgeid, edgecolor) :: _ =>
  let
    val _ = queue := tl (!queue)    
    val (_, (blue_clauses, red_clauses)) = Vector.sub (assignv,edgeid)
      handle Subscript => raise ERR "assignv" (ets (edgeid,edgecolor))
    val (clauses_prop,clauses_del) = 
      if edgecolor = blue then (blue_clauses, red_clauses) 
                          else (red_clauses, blue_clauses)
    fun f_prop (clauseid,litid) = 
      let
        fun msg () = its clauseid ^ " " ^ its litid
        (* val _ = debugf "clause: " msg () *)
        val (clausev,nref) = Vector.sub (clausevv,clauseid)
          handle Subscript => raise ERR "clausevv" (its clauseid)
        val (bref,_) = Vector.sub (clausev,litid)
          handle Subscript => raise ERR "clausev" (its litid)
        val _ = if !bref
                then raise ERR "propagate_sat" "bref not reset"
                else ()
        val _ = (bref := true; incr nref)
        val _ = undol := (fn () => (bref := false; decr nref)) :: !undol
      in
        (* happens if a clause contains only one literal *)
        (* find a better way to exit that raising an exception *)
        if !nref > Vector.length clausev - 1 then raise Conflict else
        if !nref < Vector.length clausev - 1 then () else
        let 
          (* val _ = debug "propagated" *)
          val ((newedgeid,_),tempcolor) = propagated_clause clausev
          val propcolor = 3 - tempcolor
          val assigncolor = fst (Vector.sub (assignv, newedgeid))
            handle Subscript => raise ERR "assignv" (ets (newedgeid,propcolor))
        in
          if !assigncolor = propcolor then () 
          else if !assigncolor = tempcolor then raise Conflict 
          else 
            let 
              fun msg () = ets (newedgeid, propcolor)
              val _ = debugf "prop: " msg ()
              val _ = incr prop_small_counter
            in 
              assign undol newedgeid assigncolor propcolor;
              queue := (newedgeid,propcolor) :: !queue
            end
        end
      end
    (* delete links of all unassigned literals *)  
    fun f_del (clauseid, litid) =   
      let 
        (* val _ = debug "delete" *)
        val (clausev,nref) = Vector.sub (clausevv,clauseid)
          handle Subscript => raise ERR "clausevv" (its clauseid)
        fun f (bref,((edgeid,ecid),color)) = if !bref then () else
          let 
            val bothdlv = snd (Vector.sub (assignv,edgeid))
              handle Subscript => raise ERR "assignv" (its edgeid)
            val dlv = if color = blue then fst bothdlv else snd bothdlv
            val undof = dlv_del ecid dlv
              handle Subscript => raise ERR "dlv_del" 
                (ets (edgeid,color) ^ "~" ^ its ecid)
          in 
            undol := undof :: !undol
          end
      in
        Vector.app f clausev
      end      
  in
    case 
      ((dlv_app f_prop clauses_prop; 
        dlv_app f_del clauses_del;
       NONE) 
      handle Conflict => SOME (!undol,true))
    of
      NONE => (* debug "prop loop"; *) 
        prop_sat_loop assignv clausevv queue undol
    | SOME s => s
  end
  

fun prop_sat assignv clausevv (edgeid,color) =
  let 
    val undol = ref []
    val assignref = fst (Vector.sub (assignv,edgeid))
      handle Subscript => raise ERR "assignv" (ets (edgeid,color))
    val queue = ref [(edgeid,color)]
  in
    assign undol edgeid assignref color;
    prop_sat_loop assignv clausevv queue undol
  end

(* -------------------------------------------------------------------------
   Decision
   ------------------------------------------------------------------------- *)

fun rotate n l = 
  let val (l1,l2) = part_n n l in l2 @ l1 end

fun next_assign_aux assignv vl =   
  let 
    fun test vi = 
      let val (a,(dv1,dv2)) = Vector.sub (assignv,vi) in
        !a = 0 (* andalso
        (not (dlv_null dv1 andalso dlv_null dv2)) *)
      end
    val avl = filter test vl
  in
    if null avl then NONE else SOME (hd avl)
  end
    
fun next_assign assignv =  
  (next_assign_aux assignv (!edgel_glob),[red,blue])


(* -------------------------------------------------------------------------
   Degree test
   ------------------------------------------------------------------------- *)

(* degree *)
fun degree_geq n color graph x = 
  length (neighbor_of color graph x) >= n

(* fun test_degree (edgeid,color) =
  let
    val _ = incr degree_counter
    val graph  = !graph_glob
    val degree_limit = if color = red then 13 else 5
    val (a,b) = var_to_edge edgeid
    val reda = neighbor_of red graph a 
    val redb = neighbor_of red graph b 
    fun test (x,y) = length (commonneighbor_of red graph (x,y)) >= 9
  in
    degree_geq degree_limit color graph a orelse 
    degree_geq degree_limit color graph b orelse
    (if
    (color = red andalso 
     (test (a,b) orelse 
      exists (fn x => test (a,x)) reda orelse
      exists (fn x => test (b,x)) redb)
    )
    then (incr other_counter; true)
    else false)
  end
*)

fun test_degree (edgeid,color) =
  let
    val _ = incr degree_counter
    val graph  = !graph_glob
    val degree_limit = 
      if color = red then !max_red_degree else !max_blue_degree
    val (a,b) = var_to_edge edgeid
  in
    degree_geq degree_limit color graph a orelse 
    degree_geq degree_limit color graph b
  end


(* -------------------------------------------------------------------------
   Sat solver
   ------------------------------------------------------------------------- *)

exception SatTimeout;
exception Satisfiable;

fun sat_solver_loop assignv clausevv path = 
  case path of 
    [] => stats ()
  | (undol,_,[]) :: parentl => 
    (
    debug "undo"; 
    app (fn f => f ()) undol;
    sat_solver_loop assignv clausevv parentl
    )
  | (undol, eido, color :: colorm) :: parentl =>    
  (
  case eido of
    NONE => 
      (
      graphl := normalize_nauty (!graph_glob) :: !graphl;
      if !allsat_flag 
      then sat_solver_loop assignv clausevv ((undol,eido,[]) :: parentl)
      else stats ()
      )
  | SOME eid =>
     let val _ = debugf "split: " ets (eid,color) in
     if !degree_flag andalso total_time degree_timer test_degree (eid,color)
     then (debug "degree"; 
           incr degree_conflict_counter;
           sat_solver_loop assignv clausevv ((undol,eido,colorm) :: parentl)) 
     else
     let 
       val _ = incr prop_counter
       val _ = if abstract_time > 0 andalso 
          !prop_counter + !prop_small_counter > abstract_time
               then raise SatTimeout else ()
       val (newundol,conflict) = 
         total_time prop_timer (prop_sat assignv clausevv) (eid,color)
         handle Subscript => raise ERR "prop_sat" "subscript"
     in
       if conflict then 
          (
          debug "conflict";
          incr prop_conflict_counter;
          app (fn f => f ()) newundol;
          sat_solver_loop assignv clausevv ((undol,eido,colorm) :: parentl)
          )
       else if !iso_flag andalso is_iso (!graph_glob) then
          (
          debug "iso";
          app (fn f => f ()) newundol;
          sat_solver_loop assignv clausevv ((undol,eido,colorm) :: parentl)
          )   
       else 
         let val (neweido,newcolorl) = next_assign assignv in
            sat_solver_loop assignv clausevv
               ((newundol, neweido, newcolorl) :: 
                (undol,eido,colorm) :: parentl) 
         end
     end end
  )
  
fun sat_solver size (bluesize,redsize) =
  let
    val _ = init_timer ()
    val _ = isod_glob := eempty IntInf.compare
    val _ = edgel_glob := map edge_to_var (search_order_undirected size)
    val _ = edgel_n := length (!edgel_glob)
    val (assignv,clausevv) = init_sat size (bluesize,redsize)
    val (eido,colorl) = next_assign assignv
    val path = [([],eido,colorl)]
    val _ = log ("variables: " ^ its (Vector.length assignv))
    val _ = log ("clauses: " ^ its (Vector.length clausevv))
  in
    sat_solver_loop assignv clausevv path
  end
  
  
fun sat_solver_edgecl edgecl size (bluesize,redsize) =
  let
    val _ = init_timer ()
    val _ = isod_glob := eempty IntInf.compare
    val _ = edgel_glob := map edge_to_var (pairbelowy (size - 1))
    val _ = edgel_n := length (!edgel_glob)
    val (assignv,clausevv) = init_sat size (bluesize,redsize)
    fun f (edge,color) = let val (_,conflict) = 
        prop_sat assignv clausevv (edge_to_var edge, color) 
      in
        if conflict then raise ERR "sat_solver_edgecl" "conflict" else ()
      end
    val _ = app f edgecl
    val (eido,colorl) = next_assign assignv
    val path = [([],eido,colorl)]
    val _ = log ("variables: " ^ its (Vector.length assignv))
    val _ = log ("clauses: " ^ its (Vector.length clausevv))
  in
    sat_solver_loop assignv clausevv path
  end


end (* struct *)

(*
PolyML.print_depth 0;
load "sat"; open aiLib kernel graph sat;
PolyML.print_depth 10;
allsat_flag := true;
val (r,t) = add_time (sat_solver 6) (4,5);
load "gen"; open gen;
gen_width := 5;
val (cover,coverl) = split (compute_hcover r);

val gendesc7 = map_assoc (all_leafs) gen7;

exception Break;
val ERR = mk_HOL_ERR "test";
fun split_last m = 
  let 
    val size = mat_size m
    val m1 = mat_copy m
    val m2 = mat_copy m
    val l = rev (search_order_undirected size)
    fun f (i,j) = 
      if mat_sub (m,i,j) = 0 
      then (mat_update_sym (m1,i,j,blue); 
            mat_update_sym (m2,i,j,red); raise Break)
      else ()
  in
    app f l handle Break => ();
    [m1,m2]
  end;

fun harmonize_one minhole m =
  let val nhole = number_of_holes m in
    if nhole < minhole then raise ERR "harmonize_one" ""
    else if nhole = minhole then [m]
    else List.concat (map (harmonize_one minhole) (split_last m))
  end;
  
fun harmonize_holes ml =
  let 
    val minhole = list_imin (map number_of_holes ml) 
    val l = List.concat (map (harmonize_one minhole) ml)
  in
    nauty_set l
  end;
 
val coverhar = harmonize_holes cover; 


  
fun all_models cover =
  let fun f m = sat_solver_edgecl (mat_to_edgecl m) 7 (4,5) in
    nauty_set (List.concat (map f cover))
  end;
    
val model2 = all_models cover; length model2;
val model2h= harmonize_holes model2; length model2h;

val (cover2,coverl2) = split (compute_hcover model2h);


val m = hd cover;
val edgecl = 
val (model2,t1) = add_time 





*)


