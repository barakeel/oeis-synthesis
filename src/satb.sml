structure satb :> satb =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty rconfig
val ERR = mk_HOL_ERR "satb"

fun debug_mat m = if !debug_flag then graph.print_mat m else ()

(* flags conspiring to output all models *)
val allsat_flag = ref true
val degree_flag = ref false
val max_blue_degree = ref 0
val max_red_degree = ref 0
val iso_flag = ref true
val proof_flag = ref true
val graphl = ref []
val graphl_n = ref 0

fun normalize_nauty_wperm x = 
  if !iso_flag then nauty.normalize_nauty_wperm x else (x,[])

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val edgel_glob = ref []
val edgel_n = ref 0
val limit_glob = 
  (if abstract_time > 0 then SOME abstract_time else NONE, 
   if real_time > 0.0 then SOME (Time.fromReal real_time) else NONE)
val timer = ref (Timer.startRealTimer ())
val isod_glob = ref (dempty IntInf.compare: (IntInf.int, thm * int list) dict)
val prop_glob = ref (dempty Int.compare)

val graph_glob = ref (Array2.array (1,1,~1))
val reason_glob = ref (Array.array (1,~1))
val thmv_glob = ref (Vector.fromList ([]: thm list))
(* val decision_glob = ref (~1,~1)
val dec_glob = ref (Array.array (1,false));  *)
val final_thm = ref TRUTH
val gthmd_glob = ref (dempty IntInf.compare: (IntInf.int, thm) dict)
val size_glob = ref 0
val pos_thm = ref TRUTH
val neg_thm = ref TRUTH

val empty_il = [] : int list
val empty_iil = [] : (int * int) list
val empty_iv = Vector.fromList empty_il
val block_thm = ref TRUTH
val learna_free = ref 0
val learna = ref (Array.array (1,(empty_iv, TRUTH)))
val watcha = ref (Array.array (1, empty_iil))
val w_upl = ref empty_il

fun init_wla watchsize learnsize =
  (
  watcha := Array.array (watchsize,empty_iil);
  learna := Array.array (learnsize,(empty_iv, TRUTH));
  learna_free := 0
  )
  

fun get_color assignv v = !(fst (Vector.sub (assignv,v)))
fun get_lit assignv v = (v, get_color assignv v)


(* 
fun prev_dec v = 
  let val newv = v-1 in
    if newv < 0 then NONE else
    if Array.sub (!dec_glob, newv) then SOME newv else prev_dec newv
  end
*)
    
fun next_dec assignv v = 
  let val newv = v+1 in
    if newv >= Vector.length assignv then NONE else
    if get_color assignv newv = 0 then SOME newv else next_dec assignv newv
  end

fun string_of_clause clause = 
  let fun f (v,c) = its v ^ ":" ^ its c in
    String.concatWith " " (map f clause)
  end  

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
val iso_conflict_counter = ref 0
val norm_failure = ref 0
val degree_counter = ref 0
val degree_timer = ref 0.0
val degree_conflict_counter = ref 0

val other_counter = ref 0
val other_timer = ref 0.0

fun init_timer () =
  (
  show_assums := true;
  final_thm := TRUTH;
  gthmd_glob := dempty IntInf.compare;
  graphl_n := 0;
  graphl := [];
  prop_counter := 0;
  prop_small_counter := 0;
  prop_conflict_counter := 0;
  prop_timer := 0.0;
  iso_counter := 0;
  iso_timer := 0.0;
  iso_conflict_counter := 0;
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
       its (!iso_conflict_counter) ^ " conflicts, " ^
       rts_round 6 (!iso_timer) ^ " seconds, " ^
       rts_round 6 (!iso_timer2) ^ " seconds"
       );
  log ("degree: " ^ its (!degree_counter) ^ " calls, " ^ 
                    its (!degree_conflict_counter) ^ " conflicts, " ^ 
                    rts_round 6 (!degree_timer) ^ " seconds");       
  log ("other: " ^ its (!other_counter) ^ " calls, " ^ 
                   rts_round 6 (!other_timer) ^ " seconds");    
  log ("learn: " ^ its (!learna_free) ^ " learned clauses");
  log ("intermediate: " ^ its (!graphl_n));
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
   Conversion between edges and variables
   ------------------------------------------------------------------------- *)

val vartoedgev = Vector.fromList (search_order_undirected 50);

fun var_to_edge x = Vector.sub (vartoedgev,x) 
  (* handle Subscript => raise ERR "var_to_edge" (its x) *)

fun edge_to_var (x,y) = 
  if x < y then x + ((y * (y - 1)) div 2) else 
  raise ERR "edge_to_var" (its x ^ "-" ^ its y)


(* -------------------------------------------------------------------------
   Syntax
   ------------------------------------------------------------------------- *)

val E = mk_var ("E",``:num -> num -> bool``)
fun X i = mk_var ("x" ^ its i,``:num``)
fun Xnum x = (string_to_int o tl_string o fst o dest_var) x
fun hvarij (i,j) = list_mk_comb (E,[X i,X j]);
fun hvar v = hvarij (var_to_edge v)
fun is_lit tm = 
  let val tm' = if is_neg tm then dest_neg tm else tm in
    term_eq (fst (strip_comb tm')) E 
  end
  
fun hlit (v,c) = 
  if c = 1 then hvar v else 
  if c = 2 then mk_neg (hvar v) 
  else raise ERR "hlit" "" ;

fun hlit_to_edge tm = 
  let 
    val tm' = if is_neg tm then dest_neg tm else tm
    val (_,argl) = strip_comb tm'
  in
    pair_of_list (map Xnum argl)
  end
  handle HOL_ERR e => (print_endline (term_to_string tm); raise HOL_ERR e)

fun hlit_to_var tm = edge_to_var (hlit_to_edge tm)
fun hlit_to_vc tm = (hlit_to_var tm, if is_neg tm then red else blue)
fun hlit_to_vci tm = 2 * hlit_to_var tm + (if is_neg tm then 1 else 0)
  


fun noclique n (cliquen,b) = 
  let
    val vl = List.tabulate (cliquen,X)
    fun f v = numSyntax.mk_less (v,numSyntax.term_of_int n);
    val boundl = map f vl
    val pairvl = map pair_of_list (subsets_of_size 2 vl)
    val litl = map (fn (a,b) => list_mk_comb (E,[a,b])) pairvl
    val diffl = map (fn (a,b) => mk_neg (mk_eq (a,b))) pairvl  
    val litl' = map (fn x => if b then x else mk_neg x) litl
  in
    list_mk_forall (vl, list_mk_imp (boundl @ diffl @ litl',F)) 
  end;

(*
load "sat"; open sat;
val tm = noclique 6 (3,true);
val tm = noclique 6 (3,false);
*)

(* -------------------------------------------------------------------------
   Proof reconstruction in HOL
   ------------------------------------------------------------------------- *)

fun init_thms size (bluen,redn) =
  let
    val postm = noclique size (bluen,true)
    val negtm = noclique size (redn,false)
  in
    pos_thm := ASSUME postm;
    neg_thm := ASSUME negtm
  end

fun thm_of_graph graph = 
  let
    val edgecl = mat_to_edgecl graph
    val litl = map hlit (map_fst edge_to_var edgecl)
    val vl = List.tabulate (mat_size graph,X)
    val tm = list_mk_forall (vl, list_mk_imp (litl,F))
    val thm = UNDISCH_ALL (SPEC_ALL (ASSUME tm))
    val _ = debug "graph"
    val _ = debug_mat graph
    val _ = debugf "thm_of_graph" thm_to_string thm  
  in
    thm
  end
  handle HOL_ERR _ => raise ERR "thm_of_graph" ""


fun thm_of_clause clause = 
  let 
    val b = snd (hd clause) = blue 
    fun f (a,b) = [a,b] 
    val edgel = map (var_to_edge o fst) clause
    val vertl = mk_fast_set Int.compare (List.concat (map f edgel))
    val thm = if b then !pos_thm else !neg_thm
  in
    UNDISCH_ALL (SPECL (map X vertl) thm) handle HOL_ERR _ =>
    (
    print_endline (string_of_clause clause);
    print_endline (thm_to_string thm);
    print_endline (ilts vertl);
    raise ERR "thm_of_clause" ""
    )
  end
  
fun thm_of_assignv assignv =
  let 
    fun f (i,x) = (i,!(fst x))
    val clause = vector_to_list (Vector.mapi f assignv)
  in
    thm_of_clause clause
  end

fun SMART_DISCH v thm = 
  if v < 0 then raise ERR "SMART_DISCH" (its v) else
  let 
    val var = hvar v
    val hypl = hyp thm 
  in 
    if tmem var hypl 
      then NOT_INTRO (DISCH var thm)
    else if tmem (mk_neg var) hypl
      then CCONTR var thm
    else thm
      (* (
      print_endline (
        term_to_string var ^ " not in " ^ 
        String.concatWith ", " (map term_to_string hypl));
      raise ERR "SMART_DISCH" ""
      ) *)
  end
  
fun CONFLICT_AUX thm1 thm2 =
  if term_eq (concl thm1) F then thm1 
  else if term_eq (concl thm2) F then thm2
  else if is_neg (concl thm1) 
    then MP thm1 thm2 
    else MP thm2 thm1

fun CONFLICT thml = case thml of
    [thm] => thm
  | [thma,thmb] => CONFLICT_AUX thma thmb
  | _ => raise ERR "CONFLICT" ""


fun SAVE_ISO' ((normgraph,perm),thm) = 
  let val graphi = zip_mat normgraph in
    case dfindo graphi (!isod_glob) of
      NONE => 
       (debug_mat normgraph;
        print_endline (thm_to_string thm);
        raise ERR "SAVE_ISO" "delivered too early")
    | SOME (t,_) => 
        if term_eq (concl t) T
        then isod_glob := dadd graphi (thm,perm) (!isod_glob)
        else (debug_mat normgraph;
              print_endline (thm_to_string thm);
              raise ERR "SAVE_ISO" "should not save the same graph again")
  end
  
fun SAVE_ISO ((normgraph,perm),thm) =
  if !iso_flag then SAVE_ISO' ((normgraph,perm),thm) else ()


fun SAFE_PROVE_HYP thm1 thm2 = 
  if !debug_flag then PROVE_HYP thm1 thm2 else
  if tmem (concl thm1) (hyp thm2) 
  then PROVE_HYP thm1 thm2
  else (print_endline (thm_to_string thm1);
        print_endline (thm_to_string thm2);
        raise ERR "SAFE_PROVE_HYP" "")

fun prop_thmo v = 
  let val reasonid = Array.sub (!reason_glob,v) in
    if reasonid < 0 then NONE else
    let val thm = SMART_DISCH v (Vector.sub (!thmv_glob,reasonid)) in
      SOME thm
    end
  end

fun BACK_PROP_AUX decv thm ovl = 
  case ovl of [] => thm | v :: m =>
  (
  case prop_thmo v of 
    NONE => raise ERR "prop_thmo" (its v)
            (* BACK_PROP_AUX decv thm m *) 
  | SOME lemma =>
    let 
      val newvl = filter (fn x => x > decv) 
        (map hlit_to_var (filter is_lit (hyp lemma)))
      val newm = rev (mk_fast_set Int.compare (newvl @ m))
      val newthm = SAFE_PROVE_HYP lemma thm
    in
      BACK_PROP_AUX decv newthm newm
    end
  )

(* Eliminate all the variables strictly larger than decv *) 
fun BACK_PROP' decv thm =
  let val vl = rev (dict_sort Int.compare (filter (fn x => x > decv) 
    (map hlit_to_var (filter is_lit (hyp thm)))))
  in
    BACK_PROP_AUX decv thm vl
  end

fun BACK_PROP decv thm = total_time degree_timer (BACK_PROP' decv) thm

fun dec_thm decv (confv,confclause) = case prop_thmo confv of 
    NONE => raise ERR "dec_thm" "should not happen because of deletion"
    (*
    let 
      val thmF = Vector.sub (!thmv_glob,confclause) 
      val _ = debugf "reason: " thm_to_string thmF
    in
      SMART_DISCH decv (BACK_PROP decv thmF) 
    end
    *)
  | SOME thm1 => 
    let     
      val _ = debugf "old reason: " thm_to_string thm1
      val thm2 = SMART_DISCH confv (Vector.sub (!thmv_glob,confclause))
      val _ = debugf "new reason: " thm_to_string thm2
      val thmF = CONFLICT [thm1,thm2]
      val _ = debugf "conflict: " thm_to_string thmF
    in
      SMART_DISCH decv (BACK_PROP decv thmF) 
    end
    
fun learn_thm decv thmF =
  let val _ = debugf "conflict: " thm_to_string thmF in
    SMART_DISCH decv (BACK_PROP decv thmF) 
  end

(* -------------------------------------------------------------------------
   Safety checks
   ------------------------------------------------------------------------- *)

fun ordered_lit lit =
  let val (i,j) = hlit_to_edge lit in i < j end

fun ordered_litl litl = 
  list_compare Term.compare (dict_sort Term.compare litl, litl) = EQUAL

fun check_thmF assignv thmF = 
  let 
    val vcl = map hlit_to_vc (filter is_lit (hyp thmF))
    fun test (v,c) = get_color assignv v = c
  in
    if all test vcl then () else 
    (
    debug_mat (!graph_glob);
    print_endline (thm_to_string thmF);
    raise ERR "check_thmF" ""
    )
  end

(* -------------------------------------------------------------------------
   Test isomorphism
   ------------------------------------------------------------------------- *)

val NOT_NOT = CONJUNCT1 boolTheory.NOT_CLAUSES;
val E_SYM = 
  ASSUME ``!(x:num)(y:num). (E x y : bool) = E y x``;
val E_SYM_NOT = 
  GENL [``x:num``,``y:num``] (AP_TERM negation (SPEC_ALL E_SYM));

(*
load "sat"; open sat;
fun Xnum x = (string_to_int o tl_string o fst o dest_var) x
val lit = ``~E (x3:num) (x0:num)``;
*)

fun NORM_HYP lit =
  if not (is_lit lit) then NONE else
  let 
    val atom = if is_neg lit then dest_neg lit else lit
    val (xi,xj) = pair_of_list (snd (strip_comb atom))
  in 
    if Xnum xi < Xnum xj 
    then NONE
    else SOME ((UNDISCH o snd o EQ_IMP_RULE o SPECL [xi,xj])
      (if is_neg lit then E_SYM_NOT else E_SYM))
  end;

fun PERMUTE_LIT' thm1 perm1 perm2 = 
  let 
    val vertexl = List.tabulate (!size_glob, I)
    fun permf x = ((mk_permf perm2) o mk_permf (invert_perm perm1)) x
    fun f i = let val i' = permf i in
        if i <> i' then SOME {redex = X i, residue = X i'} else NONE
      end
    val sub = List.mapPartial f vertexl
    val thm2 = INST sub thm1
    val lemmal = (List.mapPartial NORM_HYP) (hyp thm2)
    val thm3 =(foldl (uncurry SAFE_PROVE_HYP) thm2) lemmal
  in
    thm3
  end
  
fun PERMUTE_LIT thm1 perm1 perm2 = (PERMUTE_LIT' thm1 perm1) perm2 
   
fun by_iso_aux (normgraph,perm2) =
  let val graphid = zip_mat normgraph in
    case dfindo graphid (!isod_glob) of
      NONE => (isod_glob := dadd graphid (TRUTH,[]) (!isod_glob); NONE)
    | SOME (thm,perm1) => 
      if not (!proof_flag) then SOME TRUTH else 
        if term_eq (concl thm) T 
        then (debug_mat normgraph;
              raise ERR "by_iso_aux" "promise not delivered")
        else SOME (PERMUTE_LIT thm perm1 perm2)
  end
  
fun by_iso (normgraph,perm2) =
  if !iso_flag 
  then (incr iso_counter; total_time iso_timer by_iso_aux (normgraph,perm2))
  else NONE
  

  
(* -------------------------------------------------------------------------
   Doubly-linked vector with constant time deletion
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
   Debug
   ------------------------------------------------------------------------- *)

fun cts c = 
  if c = 1 then "b" 
  else if c = 2 then "r"
  else if c = 0 then "w"
  else raise ERR "cts_color" (its c)

fun ets (a,b) = its a ^ "-" ^ its b
val vts = ets o var_to_edge
fun vcts (v,c) = vts v ^ ":" ^ cts c

fun string_of_clausev clausev = 
  let fun f (bref,lit) = bts (!bref) ^ "@" ^ vcts (fst (fst lit), snd lit) in
    String.concatWith " " (map f (vector_to_list clausev))
  end

fun string_of_assignv assignv = 
  let 
    val l1 = map (! o fst) (vector_to_list assignv)
    val l2 = number_fst 0 l1
  in
    String.concatWith " " (map vcts l2)
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
   Move clauses into an efficient data structure for propagation
   ------------------------------------------------------------------------- *)

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

fun init_sat size (bluen,redn) =
  let
    val maxedge = (size * (size - 1)) div 2
    val assignv = Vector.tabulate (maxedge, (fn _ => (ref [], ref [])))
    val clausevv = Vector.fromList []
    val clausel = ramsey_clauses size (bluen,redn)
    val (newassignv,newclausevv) = add_clausel clausel (assignv,clausevv)
    val clausev' = Vector.map (Vector.map (fn ((a,b),c) => (a,c))) newclausevv;
    val clausel_alt = map vector_to_list (vector_to_list clausev');
    val _ = if clausel = clausel_alt then () else 
      raise ERR "init_sat" "unexpected"
    val _ = init_thms size (bluen,redn)
    val _ = thmv_glob := Vector.fromList (map thm_of_clause clausel)
    val _ = graph_glob := Array2.array (size,size,0)
    val _ = reason_glob := Array.array (Vector.length newassignv, ~1)
  in
    transform_pb (newassignv,newclausevv)
  end

(* -------------------------------------------------------------------------
   Propagation
   ------------------------------------------------------------------------- *)

exception Conflict of (int * int)

fun propagated_clause clausev = 
  let fun loop i = 
    let val (bref,lit) = Vector.sub (clausev,i) in
      if not (!bref) then lit else loop (i+1)
    end
  in
    loop 0
  end
  handle Subscript => raise ERR "propagated_clause" (string_of_clausev clausev)

fun vc_to_int (edgeid,color) = 
  2 * edgeid + (if color = blue then 0 else 1)

fun assign undol edgeid assignref color =
  let 
    val graph = !graph_glob
    val (a,b) = var_to_edge edgeid
    fun back () = (assignref := 0; mat_update_sym (graph,a,b,0))  
  in
    w_upl := vc_to_int (edgeid,color) :: !w_upl;
    assignref := color;
    mat_update_sym (graph,a,b,color);
    undol := back :: !undol
  end
  handle HOL_ERR _ => raise ERR "assign" ""

fun prop_sat_loop assignv clausevv queue undol = case !queue of 
    [] => (!undol, false, (~1,~1))
  | (edgeid, edgecolor) :: _ => 
  let
    val _ = queue := tl (!queue)    
    val (_, (blue_clauses, red_clauses)) = Vector.sub (assignv,edgeid)
      handle Subscript => raise ERR "assignv" (vcts (edgeid,edgecolor))
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
        if !nref > Vector.length clausev - 1 then 
          raise ERR "unit clause" "not supported" 
        else
        if !nref < Vector.length clausev - 1 then () else
        let 
          (* val _ = debug "propagated" *)
          val ((confv,_),tempcolor) = propagated_clause clausev
          val propcolor = 3 - tempcolor
          val assigncolor = fst (Vector.sub (assignv, confv))
            handle Subscript => raise ERR "assignv" (vcts (confv,propcolor))
        in
          if !assigncolor = propcolor then () 
          else if !assigncolor = tempcolor then 
            (debug "conflict"; raise Conflict (confv,clauseid))
          else 
            let 
              fun msg () = vcts (confv, propcolor)
              val _ = debugf "prop: " msg ()
              val _ = incr prop_small_counter
              val _ = Array.update (!reason_glob,confv,clauseid)
              fun undof () = Array.update (!reason_glob,confv,~1)
              val _ = undol := undof :: !undol
            in 
              assign undol confv assigncolor propcolor;
              queue := (confv,propcolor) :: !queue
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
                (vcts (edgeid,color) ^ "~" ^ its ecid)
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
      handle Conflict (confv,confclause) => 
        SOME (!undol,true,(confv,confclause)))
    of
      NONE => (* debug "prop loop"; *) 
        prop_sat_loop assignv clausevv queue undol
    | SOME s => s
  end

fun prop_sat assignv clausevv (edgeid,color) =
  let
    val undol = ref []
    val _ = w_upl := []
    (*
    val _ = decision_glob := (edgeid,color)
    val _ = Array.update (!dec_glob, edgeid, true)
    fun undof () = Array.update (!dec_glob, edgeid, false)
    val _ = undol := undof :: !undol
    *)
    val assignref = fst (Vector.sub (assignv,edgeid))
      handle Subscript => raise ERR "assignv" (vcts (edgeid,color))
    val queue = ref [(edgeid,color)]    
  in
    assign undol edgeid assignref color;
    prop_sat_loop assignv clausevv queue undol
  end

(* -------------------------------------------------------------------------
   Blocking clauses (poor man CDCL): 
   update the watch literal in each learned clause.
   Learned clause are only preventing the exploration of branches
   and not propagating.
   ------------------------------------------------------------------------- *)

exception Break

fun is_free assignv w = get_color assignv (w div 2) <> 1 + w mod 2

fun next_pos_aux assignv clausev porg x = 
  if x >= Vector.length clausev then next_pos_aux assignv clausev porg 0
  else if x = porg then NONE   
  else if is_free assignv (Vector.sub (clausev,x)) then SOME x
  else next_pos_aux assignv clausev porg (x + 1)

fun next_pos assignv clausev porg = 
  next_pos_aux assignv clausev porg (porg + 1)

fun find_pos assignv clausev x = 
  if x >= Vector.length clausev then NONE 
  else if is_free assignv (Vector.sub (clausev,x)) then SOME x
  else find_pos assignv clausev (x + 1)

fun update_watch clausev (clause,pos) =
  let 
    val neww = Vector.sub (clausev,pos) 
    val newclausel = (clause,pos) :: Array.sub (!watcha,neww)
  in
    Array.update (!watcha, neww, newclausel)
  end  

fun blocking_aux assignv =
  let
    fun update_watch_top w = 
      let 
        val clausel = Array.sub (!watcha,w)
        fun f (clause,pos) = 
          let 
            val (clausev,thm) = Array.sub (!learna,clause) in
            case next_pos assignv clausev pos of
              NONE => (block_thm := thm; raise Break) 
            | SOME newpos => update_watch clausev (clause,newpos)
          end   
      in
        app f clausel
      end
  in
    app update_watch_top (!w_upl);
    app (fn w => Array.update (!watcha,w,[])) (!w_upl)
  end

fun blocking assignv = 
  (blocking_aux assignv; false) handle Break => true 


fun clausev_of_thm thm =
  if not (term_eq (concl thm) F) then raise ERR "thm_to_clause" "" else
  let val litl = filter is_lit (hyp thm) in
    Vector.fromList (map hlit_to_vci litl)
  end

fun update_wla assignv thm =
  let 
    val clause = !learna_free
    val clausev = clausev_of_thm thm
    val _ = debug_mat (!graph_glob)
    val _ = debugf (its clause ^ ": ") thm_to_string thm
  in
    if clause >= Array.length (!learna)
      then raise ERR "update_wla" "limit reached" else
    (
    case find_pos assignv clausev 0 of
      NONE => false
    | SOME pos => 
      (
      if Vector.length clausev >= 40 then () else
       (Array.update (!learna, clause, (clausev,thm));
       incr learna_free; 
       update_watch clausev (clause,pos))
      ;
      true
      )
    )
  end

(* -------------------------------------------------------------------------
   Sat solver
   ------------------------------------------------------------------------- *)

exception SatTimeout;
exception Satisfiable;

val colorl_glob = [red,blue]

fun msg_split (decv,color) =
  let
    val _ = debug_mat (!graph_glob)
    val _ = debugf "split: " vcts (decv,color)
    val _ = incr prop_counter
  in
    ()
  end

fun time_out () =
  if abstract_time > 0 andalso 
     !prop_counter + !prop_small_counter > abstract_time
  then raise SatTimeout else ()

(* can backtrack to parents of parents and so on *)
fun backtrack assignv clausevv path =
  case path of (undol1,_,[],thml1,g1) :: 
    (undol2,decv,colorl,thml2,g2) :: parentl => 
  let
    val _ = debugf "decv: " vts decv
    val thmF' = if not (!proof_flag) then TRUTH else 
      let
        val thmF = CONFLICT thml1
        val _ = SAVE_ISO (g1,thmF)   
      in
        BACK_PROP decv thmF
      end
    val decthm = if not (!proof_flag) then TRUTH else SMART_DISCH decv thmF'
    val _ = (debug "undo"; app (fn f => f ()) undol1)  
    val r = update_wla assignv thmF'
  in
    if r 
    then (undol2, decv, colorl, decthm :: thml2, g2) :: parentl
    else (
         if term_eq (concl decthm) F then () 
         else raise ERR "backtrack" "unexpected";
         debug "undo-jump";
         backtrack assignv clausevv
         ((undol2, decv, [], decthm :: thml2, g2) :: parentl)
         )
  end
  | _ => path
   
   
   
fun sat_solver_loop assignv clausevv path = 
  let 
    val _ = time_out ()
    fun frec x = sat_solver_loop assignv clausevv x 
  in
  case path of 
    [(undol,_,[],thml,_)] =>
    (if !proof_flag then final_thm := CONFLICT thml else ();
     stats ())  
  | (_,_,[],_,_) :: parentl => 
    let val newpath = backtrack assignv clausevv path in
      frec newpath
    end
  | (undol, decv, color :: colorm, thml, g1) :: parentl =>  
    let
     val _ = msg_split (decv,color)
     val _ = prop_glob := dadd decv (mat_copy (!graph_glob)) (!prop_glob);
     (* val _ =  *)
     val (newundol,conflict,(confv,confclause)) = 
       total_time prop_timer (prop_sat assignv clausevv) (decv,color)
       handle Subscript => raise ERR "prop_sat" "subscript"
    in
      if conflict then 
        let
          val _ = (debug "conflict: prop"; incr prop_conflict_counter)
          val decthm = if not (!proof_flag) then TRUTH else
            dec_thm decv (confv,confclause)
          val newpath = (undol,decv,colorm, decthm :: thml, g1) :: parentl  
        in
          app (fn f => f ()) newundol;
          frec newpath
        end
      else 
      if !proof_flag andalso blocking assignv then
        let
          val _ = (debug "conflict: learn"; incr degree_conflict_counter)
          val decthm = learn_thm decv (!block_thm) 
          val newpath = (undol,decv,colorm, decthm :: thml, g1) :: parentl  
        in
          app (fn f => f ()) newundol;
          frec newpath
        end
      else
      let val (normgraph,perm) = normalize_nauty_wperm (!graph_glob) in
      case by_iso (normgraph,perm) of 
        SOME thmF =>
        let
          val _ = (debug "conflict: iso"; incr iso_conflict_counter)
          val decthm = if not (!proof_flag) then TRUTH else 
            SMART_DISCH decv (BACK_PROP decv thmF)
          val newpath = (undol,decv,colorm, decthm :: thml, g1) :: parentl
        in
          app (fn f => f ()) newundol;
          frec newpath
        end
      | NONE =>
      (
      case next_dec assignv decv of 
        NONE => 
        let
          val decthm = 
            if not (!proof_flag) then TRUTH else 
            let val thmF = thm_of_graph (!graph_glob) in
              SAVE_ISO ((normgraph,perm),thmF);
              SMART_DISCH decv (BACK_PROP decv thmF)
            end
          val newpath = (undol, decv, colorm, decthm :: thml,g1) :: parentl  
        in
          debug "sat";
          graphl := normgraph :: !graphl;
          app (fn f => f ()) newundol;
          frec newpath
        end
      | SOME newdecv =>
        let
          val newpath = (undol,decv,colorm,thml,g1) :: parentl
          val newnewpath = 
            (newundol,newdecv,colorl_glob,[],(normgraph,perm)) :: newpath
        in
          frec newnewpath   
        end
      )
      end
    end
  | _ => raise ERR "sat_solver" "match"
  end
  
  
fun sat_solver size (bluen,redn) =
  let
    val _ = init_timer ()
    val _ = isod_glob := dempty IntInf.compare
    val _ = prop_glob := dempty Int.compare
    val _ = edgel_glob := map edge_to_var (search_order_undirected size)
    val _ = edgel_n := length (!edgel_glob)
    val _ = size_glob := size
    val (assignv,clausevv) = init_sat size (bluen,redn)
    val path = [([],0,colorl_glob,[],normalize_nauty_wperm (!graph_glob))]
    val _ = log ("variables: " ^ its (Vector.length assignv))
    val _ = log ("clauses: " ^ its (Vector.length clausevv))
    val _ = init_wla (2 * Vector.length assignv) 10000
  in
    sat_solver_loop assignv clausevv path
  end

fun sat_solver_edgecl edgecl size (bluen,redn) =
  let
    val _ = init_timer ()
    val _ = iso_flag := false
    val _ = proof_flag := false
    val edgel = all_edges size 
    val edgeclset = enew edge_compare (map fst edgecl)
    val edge_order = filter (fn x => not (emem x edgeclset)) edgel
    val _ = edgel_glob := map edge_to_var edge_order
    val _ = edgel_n := size
    val (assignv,clausevv) = init_sat size (bluen,redn)
    fun f (edge,color) = 
      let 
        val edgeid = edge_to_var edge
        val prevcolor = ! (fst (Vector.sub (assignv,edgeid)))
      in
        if prevcolor = color then ()
        else if prevcolor = 3 - color
          then raise ERR "sat_solver_edgecl" "conflict1"
        else 
          let val (undol,conflict,_) = 
            prop_sat assignv clausevv (edgeid,color) 
          in
            if conflict then raise ERR "sat_solver_edgecl" "conflict2" else ()
          end
      end
    val _ = app f edgecl
    val eido = next_dec assignv (~1)
    val path = [([],valOf eido,colorl_glob,[],
      normalize_nauty_wperm (!graph_glob))]
    val _ = log ("variables: " ^ its (Vector.length assignv))
    val _ = log ("clauses: " ^ its (Vector.length clausevv))
  in
    sat_solver_loop assignv clausevv path
  end  
  
fun ELIM_COND size thm = 
  let
    val sub = List.tabulate (size, fn i => {redex = X i, residue = 
      numSyntax.term_of_int i});
    val thm1 = INST sub thm;
    val arithl = filter (not o is_forall) (hyp thm1)
    val thm2 = foldl (uncurry DISCH) thm1 arithl
    val thm3 = SIMP_RULE (bool_ss ++ numSimps.ARITH_ss) [] thm2
  in
    thm3
  end 

end (* struct *)

(*
PolyML.print_depth 0;
load "satb"; open satb aiLib;
PolyML.print_depth 10;
iso_flag := true; debug_flag := false; proof_flag := true;
val (satl,t) = add_time (sat_solver 14) (3,5);



*)
