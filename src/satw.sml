structure satw :> satw =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty rconfig
val ERR = mk_HOL_ERR "satw"


(* flags conspiring to output all models *)
val allsat_flag = ref true
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
val size_glob = ref 0
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

fun init_timer () =
  (
  isod_glob := eempty IntInf.compare;
  graphl := [];
  prop_counter := 0;
  prop_small_counter := 0;
  prop_conflict_counter := 0;
  prop_timer := 0.0;
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
                  its (!prop_conflict_counter) ^ " conflicts, " ^ 
                  rts_round 6 (!prop_timer) ^ " seconds"); 
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
   Conversion between edges and variables
   ------------------------------------------------------------------------- *)

val vartoedgev = Vector.fromList (search_order_undirected 50);

fun var_to_edge x = Vector.sub (vartoedgev,x) 
  handle Subscript => raise ERR "var_to_edge" ""

fun edge_to_var (x,y) = 
  if x < y then x + ((y * (y - 1)) div 2) else 
  raise ERR "edge_to_var" (its x ^ "-" ^ its y)

fun enc_color (x,c) = if c = 1 then 2 * x else 2 * x + 1;
fun enc_edgec (e,c) = enc_color (edge_to_var e,c);
fun dec_edgec x = (var_to_edge (x div 2), (x mod 2) + 1);

fun vopp x = if x mod 2 = 0 then x + 1 else x - 1;  

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
 
(* -------------------------------------------------------------------------
   Ramsey clauses
   ------------------------------------------------------------------------- *)

fun clique_of_subset (subset,color) =
  let val edgel = all_pairs (dict_sort Int.compare subset) in
    map (fn x => (edge_to_var x, color)) edgel
  end

fun ramsey_clauses size (bluen,redn) = 
  let
    val bluesubsetl = subsets_of_size bluen (List.tabulate (size,I))
    val redsubsetl = subsets_of_size redn (List.tabulate (size,I))
    val subsetl = map_assoc (fn _ => blue) bluesubsetl @
                  map_assoc (fn _ => red) redsubsetl
  in
    map clique_of_subset subsetl
  end

(* -------------------------------------------------------------------------
   Initialization
   ------------------------------------------------------------------------- *)

fun winit size (bluen,redn) = 
  let
    val clauses1 = ramsey_clauses size (bluen,redn)
    val clauses2 = map (rev o dict_sort Int.compare o map enc_color) clauses1;
    val nvar = list_imax (List.concat clauses2) + 1
    val clausev = Vector.fromList (map Vector.fromList clauses2);
    val claused = dnew (list_compare Int.compare) (number_snd 0 clauses2);
    fun f l = first_n 2 (rev (dict_sort Int.compare l));
    val clauses21 = map_assoc f clauses2
    fun g (l1,l2) = let fun h x = (x,l1) in map h l2 end;
    val clauses22 = map g clauses21;
    val clauses3 = List.concat clauses22
    fun k (v, clause) = (v, dfind clause claused)
    val clauses4 = map k clauses3;
    val clauses41 = dlist (dregroup Int.compare clauses4);
    val clauses6d = dnew Int.compare clauses41;
    val varv = Vector.tabulate (nvar, fn i => 
      (dfind i clauses6d handle NotFound => []))
  in
    (varv,clausev)
  end

(* -------------------------------------------------------------------------
   Propagation
   ------------------------------------------------------------------------- *)

exception Conflict;


fun next_lit assigna (litv,litn) starti  =
  if starti >= litn then (~1,true) else
  let val lit = Vector.sub (litv,starti) in
    if Array.sub (assigna, vopp lit) 
      then (starti,false)
    else if not (Array.sub (assigna,lit))
    then (starti,true)
    else next_lit assigna (litv,litn) (starti + 1) 
  end;
 
fun update_ww undol litv v w1 w2 newlit = 
  if Vector.sub (litv,!w1) = v
  then 
    let val w1unref = !w1 in
      w1 := newlit;
      undol := (fn () => w1 := w1unref) :: !undol
    end
  else     
    let val w2unref = !w2 in
      w2 := newlit;
      undol := (fn () => w2 := w2unref) :: !undol
    end;

fun assign assigna undol v =
  let val _ = Array.update (assigna,v,true) in
    undol := (fn () => Array.update (assigna,v,false)) :: !undol
  end

fun wprop_loop (assigna,vara,clausev) undol queue = 
  case !queue of [] => () | v :: _ => 
  (
  let 
    val _ = queue := tl (!queue)
    val cil = Array.sub (vara,v)
    fun f ci =
      let val (litv,litn,w1,w2,del) = Vector.sub (clausev,ci) in
      if !del then () else
      let
        val starti = Int.max (!w1,!w2) + 1
        val (newlit,keep) = next_lit assigna (litv,litn) starti
      in
        if newlit < 0 then 
          let 
            val ow = if Vector.sub (litv,!w1) = v then w2 else w1
            val olit = Vector.sub (litv,!ow)
            val olitopp = vopp olit
          in
            if Array.sub (assigna,olit) then raise Conflict else
            if Array.sub (assigna,olitopp) then () else
            let val _ = queue := olitopp :: !queue in 
              assign assigna undol olitopp
            end
          end
        else if keep then
          let 
            val newv = Vector.sub (litv,newlit) 
            val newcil = Array.sub (vara,newv) 
          in
            Array.update (vara, newv, ci :: newcil);
            undol := (fn () => Array.update (vara, newv, newcil)) :: !undol;
            update_ww undol litv v w1 w2 newlit
          end
        else (del := true; undol := (fn () => del := false) :: !undol)
      end end
  in
    app f cil; 
    wprop_loop (assigna,vara,clausev) undol queue
  end
  );
  
fun wprop_one (assigna,vara,clausev) undol v = 
  if Array.sub (assigna, vopp v) then raise Conflict else
  if Array.sub (assigna, v) then () else
  let
    val _ = assign assigna undol v
    val queue = ref [v]
  in
    wprop_loop (assigna, vara, clausev) undol queue
  end  

fun wprop avc vl = 
  let val undol = ref [] in 
    (app (wprop_one avc undol) vl; (false,!undol))
    handle Conflict => (true,!undol)
  end
  

(* -------------------------------------------------------------------------
   Decision
   ------------------------------------------------------------------------- *)

fun next_splitl assigna edgel =   
  let
    fun test e =
      not (Array.sub (assigna, enc_edgec (e,1))) andalso
      not (Array.sub (assigna, enc_edgec (e,2)))
    fun f e = [[enc_edgec (e,1)],[enc_edgec (e,2)]]
  in
    Option.map f (List.find test edgel)
  end

(* -------------------------------------------------------------------------
   Recording solutions
   ------------------------------------------------------------------------- *)

fun graph_of_assigna assigna =
  let 
    val l = ref []
    fun f (v,b) = if b then l := dec_edgec v :: (!l) else ()
  in 
    Array.appi f assigna;
    edgecl_to_mat (!size_glob) (!l) 
  end

(* -------------------------------------------------------------------------
   Test isomorphism
   ------------------------------------------------------------------------- *)
    
fun is_iso path graph =
  let
    val normgraph = normalize_nauty graph
    val graphid = zip_mat normgraph
  in
    if emem graphid (!isod_glob)   
    then true
    else (isod_glob := eadd graphid (!isod_glob); false)
  end

(* -------------------------------------------------------------------------
   Sat solver
   ------------------------------------------------------------------------- *)

exception SatTimeout;
exception Satisfiable;

fun wsolve_loop (assigna,vara,clausev) edgel path =
  let fun frec x = wsolve_loop (assigna,vara,clausev) edgel x in
  case path of 
    [] => stats ()
  | (undol, NONE) :: parent => 
    (graphl := graph_of_assigna assigna :: (!graphl);
     app (fn f => f ()) undol; frec parent) 
  | (undol, SOME []) :: parent => (app (fn f => f ()) undol; frec parent)
  | (undol, SOME (vl :: splitl)) :: parent =>    
    let
      (* 
      val _ = debug ("depth: " ^ its (length path))
      val _ = debug (its (!prop_counter) ^ ": " ^ ilts vl ^ " " ^
        String.concatWith " " (map ilts splitl))
      val _ = print_mat (graph_of_assigna assigna) 
      *)
      val _ = incr prop_counter
      val (conflict,newundol) = wprop (assigna,vara,clausev) vl
         handle Subscript => raise ERR "wprop" "subscript"
      val newparent = (undol, SOME splitl) :: parent
    in
      if conflict then 
        (debug "conflict"; incr prop_conflict_counter;
         app (fn f => f ()) newundol; frec newparent) 
      else if is_iso path (graph_of_assigna assigna) 
        then (debug "iso"; app (fn f => f ()) newundol; frec newparent)
      else 
        (debug "noconflict";
         frec ((newundol, next_splitl assigna edgel) :: newparent))
     end
  end
  
fun wsolve size (bluen,redn) =
  let
    val _ = init_timer ()
    val edgel = search_order_undirected size
    val _ = size_glob := size
    val (varv,clausev) = winit size (bluen,redn) 
    val assigna = Array.array (Vector.length varv, false)  
    val vara = Array.fromList (vector_to_list varv)
    fun f x = (x, Vector.length x, ref 0, ref 1, ref false)
    val clausev' = Vector.map f clausev
    val _ = debug "split"
    val path = [([],next_splitl assigna edgel)]
    val _ = log ("var: " ^ its (Vector.length varv) ^ ", " ^
                 "cla: " ^ its (Vector.length clausev))
  in
    wsolve_loop (assigna,vara,clausev') edgel path
  end

(* -------------------------------------------------------------------------
   Glue
   ------------------------------------------------------------------------- *)

fun next_splitl_conel assigna conel path =   
  let val vertex = 14 + length path - 1 in
    if vertex >= (!size_glob) then NONE else 
    let
      val edgel = List.tabulate (14, fn i => (i,vertex))
      fun f cone = combine (edgel,cone)
      val edgecll = map f conel
      fun rm0 edgecl = filter (fn (_,c) => c <> 0) edgecl
      val edgecll' = map rm0 edgecll
    in
      SOME (number_fst 0 (map (map enc_edgec) edgecll'))
    end
  end

fun list_vars assigna =
  let 
    val l = ref []
    fun f (v,b) = 
      let val ((i,j),c) = dec_edgec v in
        if b andalso j >= 14 andalso i < 14
        then l := ((i,j),c) :: (!l) 
        else ()
      end
  in 
    Array.appi f assigna;
    (rev (!l))
  end  

val lemmal = ref [] 
fun wglue_loop (assigna,vara,clausev) m35 conel path hist =
  let fun frec x y = wglue_loop (assigna,vara,clausev) m35 conel x y in
  case path of 
    [] => stats ()
  | (undol, NONE) :: parent => 
    (
    (* graphl := graph_of_assigna assigna :: (!graphl); *)
    lemmal := ((m35,hist), SOME (list_vars assigna)) :: !lemmal;
    app (fn f => f ()) undol; frec parent (tl hist)
    ) 
  | (undol, SOME []) :: parent => (app (fn f => f ()) undol; 
    frec parent (tl hist))
  | (undol, SOME ((i,vl) :: splitl)) :: parent =>    
    let
      (* 
      val _ = debug ("depth: " ^ its (length path))
      val _ = debug (its (!prop_counter) ^ ": " ^ ilts vl ^ " " ^
        String.concatWith " " (map ilts splitl))
      val _ = print_mat (graph_of_assigna assigna) 
      *)
      val _ = incr prop_counter
      val (conflict,newundol) = 
         total_time prop_timer (wprop (assigna,vara,clausev)) vl
         handle Subscript => raise ERR "wprop" "subscript"
      val newparent = (undol, SOME splitl) :: parent
    in
      if conflict then 
        (debug "conflict"; incr prop_conflict_counter;
         lemmal := ((m35,i :: hist), NONE) :: !lemmal;
         app (fn f => f ()) newundol; frec newparent hist) 
      else if is_iso path (graph_of_assigna assigna) 
        then (debug "iso"; app (fn f => f ()) newundol; frec newparent hist)
      else 
        let 
          val newsplitlo = next_splitl_conel assigna conel path 
          val newnewparent = (newundol, newsplitlo) :: newparent
          val newhist = i :: hist 
        in
          debug "noconflict"; frec newnewparent newhist
        end
     end
  end

  
fun wglue (m44,m35) conel (bluen,redn) =
  let
    val size = mat_size m44 + mat_size m35
    val _ = init_timer ()
    val _ = size_glob := size
    val (varv,clausev) = winit size (bluen,redn) 
    val assigna = Array.array (Vector.length varv, false)  
    val vara = Array.fromList (vector_to_list varv)
    fun f x = (x, Vector.length x, ref 0, ref 1, ref false)
    val clausev' = Vector.map f clausev
    val csize = mat_size m44 
    val ecl44 = mat_to_edgecl m44
    fun shift_edgecl x ecl = map (fn ((a,b),c) => ((a + x, b + x),c)) ecl;
    val ecl35 = shift_edgecl csize (mat_to_edgecl m35)         
    val vl = map enc_edgec (ecl44 @ ecl35)
    val path = [([],SOME [(~1,vl)])]
    val _ = log ("var: " ^ its (Vector.length varv) ^ ", " ^
                 "cla: " ^ its (Vector.length clausev))             
  in
    wglue_loop (assigna,vara,clausev') m35 conel path [~2]
  end  

  

end (* struct *)

(*
PolyML.print_depth 0;
load "ramsey"; load "gen"; 
open ramsey aiLib kernel graph nauty gen rconfig;
PolyML.print_depth 10;

load "satw"; open satw aiLib;
val (l1,t1) = add_time (wsolve 10) (4,4);
load "sat"; open sat;
val (l2,t2) = add_time (sat_solver 10) (4,4);




val filel = listDir "ramsey_cone";
val m44 = sunzip_mat (hd filel);
val m35 = unzip_mat (hd (read35 10));
val conel = map stil (readl ("ramsey_cone/" ^ hd filel));
val conev = Vector.fromList conel;
val m35_3 = mat_permute (m35,3) (mk_permf [0,1,2]);
lemmal := [];
val lemmas = (ignore (wglue (m44,m35_3) conel (4,5)); !lemmal);

val conel1 = 

fun 




fun f ((a,b),c) = if isSome c then SOME (rev (first_n 2 b),valOf c) else NONE; 
val l =  List.mapPartial f lemmas;
val lemmad = dnew (list_compare Int.compare) l;
val m35_3 = mat_permute (m35,3) (mk_permf [0,1,2]);

val av1 = filter (fn x => snd x <> NONE) lemmas;
val av2 = map (snd o fst) av1;
val av3 = map (pair_of_list o rev o first_n 2) av2;
val av3' = filter (fn (a,b) => a <= b) av3;
val avd = dregroup Int.compare av3';
fun find_avd x = dfind x avd handle NotFound => [];
fun list_inter l1 l2 = filter (fn x => mem x l2) l1;
fun f (x,y) = list_inter (find_avd x) (find_avd y);
val av4 = map_assoc f av3';
val av5 = map (fn ((a,b),c) => [a,b,c]) (distrib av4);

exception Conflict;
fun intersect coloring = 
  let 
    val size = list_imax (map (snd o fst) coloring)
    val m = Array2.array (size + 1, size + 1, 0)
    fun f ((i,j),c) =
      let val oldc = mat_sub (m,i,j) in
        if oldc = 0 then mat_update_sym (m,i,j,c) else 
        if oldc = c then () else raise Conflict
      end
  in
    (app f coloring; SOME (mat_to_edgecl m)) handle Conflict => NONE
  end;   
fun permute_coloring coloring sigma  = 
   map_fst (fn (i,j) => (sigma i, sigma j)) coloring;


val av5e = hd av5;


fun sigma1 l = 
  let val d = dnew Int.compare (combine ([14,15],map fst l)) in
    (fn x => (dfind x d handle NotFound => x))
  end;

fun create_col iseq = 
  let 
    val sigma = sigma1 iseq
    val col1 = dfind (map snd iseq) lemmad;
  in
    permute_coloring col1 sigma
  end;
 
fun create_col' av5e = 
  let
    val vertexl = [14,15,16];
    val av5e2 = combine (vertexl,av5e);
    val ll = subsets_of_size 2 av5e2;
    val ll1 = map create_col ll;  
    val colo = intersect (List.concat ll1)
  in
    colo
  end;
  
val av5c = List.mapPartial create_col' av5; 
length av5; length av5c;
  
val sigmal = map sigma1 ll;



val col1 = dfind (first_n 2 av5e) lemmad;
fun sigma2 x = if x = 15 then 16 else x;
val col2 = permute_coloring (dfind [115,128] lemmad) sigma2;
fun sigma3 x = if x = 14 then 15 else if x = 15 then 16 else x;
val col3 = permute_coloring (dfind [124,128] lemmad) sigma3;


val colo = intersect (List.concat [col1,col2]);

val av6 = 


val av5  = 


(* Minisat theorem prover in HOL4 *)
PolyML.print_depth 0;
load "ramsey"; load "gen"; 
open ramsey aiLib kernel graph nauty gen rconfig;
load "sat"; open sat aiLib;
PolyML.print_depth 10;

val clauses = sat.ramsey_clauses 24 (4,5);

fun clique_of_subset (subset,color) =
  let val edgel = all_pairs (dict_sort Int.compare subset) in
    map (fn x => (x, color)) edgel
  end;

fun ramsey_clauses size (bluen,redn) = 
  let
    val bluesubsetl = subsets_of_size bluen (List.tabulate (size,I))
    val redsubsetl = subsets_of_size redn (List.tabulate (size,I))
    val subsetl = map_assoc (fn _ => blue) bluesubsetl @
                  map_assoc (fn _ => red) redsubsetl
  in
    map clique_of_subset subsetl
  end;
  
val filel = listDir "ramsey_cone";
val m44 = sunzip_mat (hd filel);
val m35 = unzip_mat (hd (read35 10));

fun diag_mat m1 m2 = 
  let
    val ecl1 = mat_to_edgecl m1;
    fun shift_edgecl x ecl = map (fn ((a,b),c) => ((a + x, b + x),c)) ecl;
    val ecl2 = shift_edgecl (mat_size m1) (mat_to_edgecl m35);
    val m = edgecl_to_mat (mat_size m1 + mat_size m2) (ecl1 @ ecl2);
  in
    m
  end;
  
fun reduce_clause mat acc clause = case clause of
    [] => SOME (rev acc)
  | (lit as ((i,j),color)) :: m => 
    let val newcolor = mat_sub (mat,i,j) in
      if newcolor = 0 then reduce_clause edgecd (lit :: acc) m
      else if color = newcolor then reduce_clause edgecd acc m else NONE
    end;

fun ramsey_clauses_wmat (bluen,redn) mat =
  List.mapPartial (reduce_clause mat []) 
    (ramsey_clauses (mat_size mat) (bluen,redn));

val coneclauses = map f columns;

val mat = diag_mat m44 m35; print_mat mat;
val clauses = ramsey_clauses_wmat (4,5) mat;

fun myvar ((i,j),r) = (if r=1 then mk_neg else I)
  (mk_var ("E_" ^ its i ^ "_" ^ its j,bool));
  
val hclauses = map (fn y => list_mk_disj (map myvar y)) clauses; 

val filel = listDir "ramsey_cone";
val m44 = sunzip_mat (hd filel);
val m35 = unzip_mat (hd (read35 10));
val conel = map stil (readl ("ramsey_cone/" ^ hd filel));

val columns = 
 List.tabulate (10,fn j => (List.tabulate (14,fn i => (i,j+14))));

val column = hd columns;

fun f column = 
  let 
    val l1 = map (fn x => combine (column,x)) conel;
    val l2 = map (fn x => list_mk_conj (map myvar x)) l1;
    val l3 = list_mk_disj l2;
  in
    l3
  end;
  

val pb = mk_neg (list_mk_conj (coneclauses @ hclauses));
load "minisatProve"; open minisatProve;
val t = snd (add_time SAT_PROVE pb);
val setcl = dict_sort edgec_compare (ecl44 @ conel14 @ conel15 @ ecl35);
(* do finger printing *)
fun rm0 edgecl = filter (fn (_,c) => c <> 0) edgecl
val ecl44 = mat_to_edgecl m44
fun shift_edgecl x ecl = map (fn ((a,b),c) => ((a + x, b + x),c)) ecl;

val edgel14 = List.tabulate (14, fn i => (i,14));
val edgel15 = List.tabulate (14, fn i => (i,15));






 
val mat = edgecl_to_mat (14 + mat_size m35_3) ecl;

val permute = 

val mat_permute (mat, mat_size mat - 1, 



load "nauty"; open nauty; 
nauty_set graphl1;



val leafl = map unzip_mat (read44 12);
val (genl,t) = add_time (compute_scover (4,4)) leafl;
writel (selfdir ^ "/ramsey_4_4_gen/12") (map szip_mat genl);

(* safety check *)
val leafl2 = mk_fast_set mat_compare leafl;
val leafl1 = mk_fast_set mat_compare (List.concat (map all_leafs genl));
all (fn x => (mat_compare x = EQUAL) (combine (leafl1,leafl2));







fun is_clique m color l = 
    let val l' = map pair_of_list (subsets_of_size 2 l) in
      all (fn (a,b) => mat_sub (m,a,b) = color) l'
    end;
val subsets = subsets_of_size 4 (List.tabulate (10,I));
val redcliques = filter (is_clique m35 red) subsets;



PolyML.print_depth 0;
load "ramsey"; load "gen"; load "sat"; 
open ramsey aiLib kernel graph sat nauty gen rconfig;
PolyML.print_depth 10;




val ecl44 = mat_to_edgecl m44;
fun shift_edgecl x ecl = map (fn ((a,b),c) => ((a + x, b + x),c)) ecl;
val ecl35 = shift_edgecl (mat_size m44) (mat_to_edgecl m35);
val graph = edgecl_to_mat 24 (ecl44 @ ecl35);



print_mat m35;
print_mat m44;
print_mat graph;



val x0 = ramsey_clauses 24 (4,5);
val x1 = map (map enc_color) x0;


val x2 =  x1;
val x3  = map (fn (l1,l2) => (map (fn x => (x,l1)) l2)) x2;

val size = 24;
val bluen = 4;
val redn = 5;


 
val (varv,clausev) = init_sat2w 24 (4,5);
 
  

    

(* 
todo: implement the propagation algorithm for that format 
don't forget to store the undos
*)  
  
val (varv,clausev) = init_sat2w 24 (4,5);  


val x1 = map (map_fst var_to_edge) x;




val r = csearch (m44,m35) conel;
*)
