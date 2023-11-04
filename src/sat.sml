(* =========================================================================
   DPLL sat solver modulo isomorphism 
   Todo : faster reconstruction of the proof 
   (e.g topologically sorting variable to avoid duplicated work)
   ========================================================================= *)

structure sat :> sat =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty rconfig bossLib
  ramseySyntax
val ERR = mk_HOL_ERR "sat"

fun debug_mat m = if !debug_flag then graph.print_mat m else ()

(* flags conspiring to output all models *)
val allsat_flag = ref true
val degree_flag = ref false
val max_blue_degree = ref 0
val max_red_degree = ref 0
val iso_flag = ref true
val proof_flag = ref true
val graphl = ref []

fun normalize_nauty_wperm x = 
  if !iso_flag then nauty.normalize_nauty_wperm x else (x,[])

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

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
val gthmd_glob = ref 
  (dempty IntInf.compare: (IntInf.int, (thm * int list)) dict)
val conep_flag = ref false
val conethmd_glob = ref 
  (dempty (list_compare Int.compare): (int list, thm) dict)


val size_glob = ref 0
val pos_thm = ref TRUTH
val neg_thm = ref TRUTH

fun get_color assignv v = !(fst (Vector.sub (assignv,v)))
fun get_lit assignv v = (v, get_color assignv v)
    
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
       "iso: " ^ its (dlength (!isod_glob)) ^ " size, " ^ 
       rts_round 6 (!iso_timer) ^ " seconds, " ^
       rts_round 6 (!iso_timer2) ^ " seconds"
       );
  log ("degree: " ^ its (!degree_counter) ^ " calls, " ^ 
                    its (!degree_conflict_counter) ^ " conflicts, " ^ 
                    rts_round 6 (!degree_timer) ^ " seconds");       
  log ("other: " ^ its (!other_counter) ^ " calls, " ^ 
                   rts_round 6 (!other_timer) ^ " seconds");
  !graphl
  )



(* -------------------------------------------------------------------------
   Permutes vertices in a theorem
   ------------------------------------------------------------------------- *)

val E_SYM = ASSUME ``!(x:num)(y:num). (E x y : bool) = E y x``
val E_SYM_NOT = GENL [``x:num``,``y:num``] (AP_TERM negation (SPEC_ALL E_SYM))

fun SAFE_PROVE_HYP thm1 thm2 = 
  if not (!debug_flag) then PROVE_HYP thm1 thm2 else
  if tmem (concl thm1) (hyp thm2) 
  then PROVE_HYP thm1 thm2
  else (print_endline (thm_to_string thm1);
        print_endline (thm_to_string thm2);
        raise ERR "SAFE_PROVE_HYP" "")

val PROVE_HYP_EQ = PROVE_HYP o UNDISCH o fst o EQ_IMP_RULE
fun PROVE_HYPL lemmal thm = foldl (uncurry PROVE_HYP) thm lemmal

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
    val permf = (mk_permf perm2) o mk_permf (invert_perm perm1)
    val _ = if !debug_flag then 
      print_endline ("perm: " ^ ilts (List.tabulate (!size_glob,permf)))
      else ()
    fun f i = let val i' = permf i in
        if i <> i' then SOME {redex = X i, residue = X i'} else NONE
      end
    val sub = total_time timer_glob4 (List.mapPartial f) vertexl
    val thm2 = total_time timer_glob1 (INST sub) thm1
    val lemmal = total_time timer_glob2 (List.mapPartial NORM_HYP) (hyp thm2)
    val thm3 = total_time timer_glob3 (PROVE_HYPL lemmal) thm2
  in
    thm3
  end
  
fun PERMUTE_LIT thm1 perm1 perm2 = (PERMUTE_LIT' thm1 perm1) perm2 


(* -------------------------------------------------------------------------
   Proof reconstruction in HOL
   ------------------------------------------------------------------------- *)

fun mk_cdef size (bluen,redn) b tm = 
  let
    val s = "C" ^ its bluen ^ its redn ^ its size ^ 
      (if b then "b" else "r")
    val v = mk_var (s,``:(num -> num -> bool) -> bool``)
    val eqtm = mk_eq (mk_comb (v,E), tm)
  in
    new_definition (s ^ "_DEF", eqtm)
  end

fun mk_both_cdef size (bluen,redn) =
  let
    val postm = noclique size (bluen,true)
    val negtm = noclique size (redn,false)
    val posdef = mk_cdef size (bluen,redn) true postm
    val negdef = mk_cdef size (bluen,redn) false negtm
  in
    (posdef,negdef)
  end  
  
(* fetching from the future *)
fun init_thms size (bluen,redn) =
  if not (!proof_flag) then () else 
  let 
    val s = "C" ^ its bluen ^ its redn ^ its size
    val f = UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL
  in
    pos_thm := f (DB.fetch "ramseyDef" (s ^ "b_DEF"));
    neg_thm := f (DB.fetch "ramseyDef" (s ^ "r_DEF"))
  end


(* return last column (without its last entry)*)
fun cone_of_graph graph = 
  let 
    val size = mat_size graph 
    val col1 = List.tabulate (size-1,fn i => (i,size -1))
    val col2 = map (fn (i,j) => mat_sub (graph,i,j)) col1 
  in
    col2
  end    

fun thm_of_graph graph =
  if !conep_flag then
    let
      val thm = dfind (cone_of_graph graph) (!conethmd_glob)
      val _ = debugf "thm_of_cone" thm_to_string thm
    in
      thm
    end
  else 
    let
      val _ = (debug "graph before"; debug_mat graph)
      val _ = debugf "graph size: " (its o mat_size) graph  
      val (normgraph,perm2) = nauty.normalize_nauty_wperm graph
      val (thm,perm1) = dfind (zip_mat normgraph) (!gthmd_glob)
      val _ = debugf "thm_of_graph" thm_to_string thm
      val _ = debugf "perm1: " ilts perm1
      val _ = debugf "perm2: " ilts perm2
      val thm' = PERMUTE_LIT thm perm1 perm2
      val _ = debugf "thm_of_graph permuted" thm_to_string thm'
    in
      thm'
    end
    handle Subscript => raise ERR "thm_of_graph" "subscript"


fun thm_of_clause clause = 
  if not (!proof_flag) then TRUTH else 
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

fun SMART_DISCH v thm = 
  if v < 0 then raise ERR "SMART_DISCH" (its v) else
  let 
    val var = hvar v
    val hypl = hypset thm 
  in 
    if HOLset.member (hypl,var)
      then NOT_INTRO (DISCH var thm)
    else if HOLset.member (hypl,mk_neg var) 
      then CCONTR var thm
    else thm
  end
  
fun CONFLICT thm1 thm2 =
  if term_eq (concl thm1) F then thm1 
  else if term_eq (concl thm2) F then thm2
  else if is_neg (concl thm1) 
    then MP thm1 thm2 
    else MP thm2 thm1


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

fun prop_thmo v = 
  let val reasonid = Array.sub (!reason_glob,v) 
    handle Subscript => raise ERR "prop_thmo" ("reason subscript: " ^ its v) 
  in
    if reasonid < 0 then NONE else
    let val thm = SMART_DISCH v (Vector.sub (!thmv_glob,reasonid)) 
      handle Subscript => raise ERR "prop_thmo" ("thmv subscript: " ^ its v) 
    in
      SOME thm
    end
  end

fun BACK_PROP_AUX decv thm ovl = 
  case ovl of [] => thm | v :: m =>
  (
  case prop_thmo v of 
    NONE => BACK_PROP_AUX decv thm m 
      (* raise ERR "prop_thmo" ("no reason for: " ^ its v) *)
  | SOME lemma =>
    let 
      (* the next two lines are really inefficient *)
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
  handle Subscript => raise ERR "BACK_PROP" ""
  
fun dec_thm decv (confv,confclause) = case prop_thmo confv of 
    NONE => raise ERR "dec_thm" "should not happen because of deletion"
    (* let 
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
      val thmF = CONFLICT thm1 thm2
      val _ = debugf "conflict: " thm_to_string thmF
    in
      SMART_DISCH decv (BACK_PROP decv thmF) 
    end

(* -------------------------------------------------------------------------
   Test isomorphism
   ------------------------------------------------------------------------- *)

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

fun clique_of_subset_f f (subset,color) =
  let val edgel = all_pairs (dict_sort Int.compare subset) in
    map (fn x => (f x, color)) edgel
  end

fun ramsey_clauses_f f size (bluen,redn) = 
  let
    val bluesubsetl = subsets_of_size bluen (List.tabulate (size,I))
    val redsubsetl = subsets_of_size redn (List.tabulate (size,I))
    val subsetl = map_assoc (fn _ => blue) bluesubsetl @
                  map_assoc (fn _ => red) redsubsetl
  in
    map (clique_of_subset_f f) subsetl
  end
  
fun ramsey_clauses_bare size (bluen,redn) = 
  ramsey_clauses_f I size (bluen,redn)
  
fun ramsey_clauses size (bluen,redn) =
  ramsey_clauses_f edge_to_var size (bluen,redn)

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

fun init_side_effects size (bluen,redn) (assignv,clausev) = 
  let
    val clausev' = Vector.map (Vector.map (fn ((a,b),c) => (a,c))) clausev;
    val clausel = map vector_to_list (vector_to_list clausev');
    val _ = init_thms size (bluen,redn)
    val _ = thmv_glob := Vector.fromList (map thm_of_clause clausel)
    val _ = graph_glob := Array2.array (size,size,0)
    val _ = reason_glob := Array.array (Vector.length assignv, ~1)
  in
    ()
  end

fun init_sat size (bluen,redn) =
  let
    val maxedge = (size * (size - 1)) div 2
    val assignv = Vector.tabulate (maxedge, (fn _ => (ref [], ref [])))
    val clausev = Vector.fromList []
    val clausel = ramsey_clauses size (bluen,redn)
    val acv = add_clausel clausel (assignv,clausev)
    val _ = init_side_effects size (bluen,redn) acv
  in
    transform_pb acv
  end
    

(* -------------------------------------------------------------------------
   Makes it so that multiple calls of the sat solver on the 
   same set of clauses takes less time
   ------------------------------------------------------------------------- *)


fun transform_pb_noref (assignv,clausevv) = 
  let fun f1 (l1,l2) = (rev (!l1), rev (!l2)) in
    (Vector.map f1 assignv, clausevv)
  end

val initsat_cache = ref (dempty (list_compare Int.compare))

fun init_sat_noref size (bluen,redn) =
  dfind [size,bluen,redn] (!initsat_cache) handle NotFound =>
  let
    val maxedge = (size * (size - 1)) div 2
    val assignv = Vector.tabulate (maxedge, (fn _ => (ref [], ref [])))
    val clausevv = Vector.fromList []
    val clausel = ramsey_clauses size (bluen,redn)
    val (newassignv,newclausevv) = add_clausel clausel (assignv,clausevv)
    val r = transform_pb_noref (newassignv,newclausevv)
  in
    initsat_cache := dadd [size,bluen,redn] r (!initsat_cache);
    r
  end
  
fun transform_pb_fromnoref (assignv,clausev) = 
  let 
    fun f1 (l1,l2) = 
      (ref 0, (dlv_fromlist (~1,~1) l1, dlv_fromlist (~1,~1) l2))
    fun f2 x = 
      (Vector.map (fn y => (ref false, y)) x, ref 0)
  in
    (Vector.map f1 assignv, Vector.map f2 clausev)
  end 

fun init_sat_fromnoref size (bluen,redn) acv = 
  let val _ = init_side_effects size (bluen,redn) acv in
    transform_pb_fromnoref acv
  end
  
fun init_sat_cached size (bluen,redn) = 
  init_sat_fromnoref size (bluen,redn) (init_sat_noref size (bluen,redn))

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
  handle HOL_ERR _ => raise ERR "assign" ""

fun prop_sat_loop assignv clausevv queue undol = case !queue of 
    [] => (!undol, false, (~1,~1))
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
        if !nref > Vector.length clausev - 1 then 
          raise ERR "unit clause" "not supported" 
        else
        if !nref < Vector.length clausev - 1 then () else
        let 
          (* val _ = debug "propagated" *)
          val ((confv,_),tempcolor) = propagated_clause clausev
          val propcolor = 3 - tempcolor
          val assigncolor = fst (Vector.sub (assignv, confv))
            handle Subscript => raise ERR "assignv" (ets (confv,propcolor))
        in
          if !assigncolor = propcolor then () 
          else if !assigncolor = tempcolor then 
            (debug "conflict"; raise Conflict (confv,clauseid))
          else 
            let 
              fun msg () = ets (confv, propcolor)
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
    val assignref = fst (Vector.sub (assignv,edgeid))
      handle Subscript => raise ERR "assignv" (ets (edgeid,color))
    val queue = ref [(edgeid,color)]    
  in
    assign undol edgeid assignref color;
    prop_sat_loop assignv clausevv queue undol
  end

(* -------------------------------------------------------------------------
   Sat solver
   ------------------------------------------------------------------------- *)

exception SatTimeout;
exception Satisfiable;

val colorl_glob = [red,blue]

fun msg_split (decv,color) =
  let
    val _ = if !debug_flag then debug_mat (!graph_glob) else ()
    val _ = debugf "split: " ets (decv,color)
    val _ = incr prop_counter
  in
    ()
  end

fun time_out () =
  if abstract_time > 0 andalso 
     !prop_counter + !prop_small_counter > abstract_time
  then raise SatTimeout else ()

fun sat_solver_loop assignv clausevv path = 
  let 
    val _ = time_out ()
    fun frec x = sat_solver_loop assignv clausevv x 
  in
  case path of 
    [(undol,_,[],[thma,thmb],_)] =>
    (if !proof_flag then final_thm := CONFLICT thma thmb else ();
     stats ())  
  | (undol,_,[],[thma,thmb],g1) :: (undol',decv,colorl,thml,g2) :: parentl => 
    let
      val decthm = if not (!proof_flag) then TRUTH else 
        let 
          val thmF = total_time degree_timer (CONFLICT thma) thmb
          val _ = SAVE_ISO (g1,thmF)   
        in
          total_time degree_timer (SMART_DISCH decv) (BACK_PROP decv thmF) 
        end
      val _ = (debug "undo"; app (fn f => f ()) undol)  
      val newparentl = (undol', decv, colorl, decthm :: thml, g2) :: parentl
    in
      frec newparentl
    end
  | (undol, decv, color :: colorm, thml, g1) :: parentl =>  
    let
     val _ = msg_split (decv,color)
     (* val _ =  *)
     val (newundol,conflict,(confv,confclause)) = 
       total_time prop_timer (prop_sat assignv clausevv) (decv,color)
       handle Subscript => raise ERR "prop_sat" "subscript"
    in
      if conflict then 
        let
          val _ = (debug "conflict"; incr prop_conflict_counter)
          val decthm = if not (!proof_flag) then TRUTH else
            dec_thm decv (confv,confclause)  
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
          val _ = (debug "iso"; incr iso_conflict_counter)
          val decthm = if not (!proof_flag) then TRUTH else 
            total_time degree_timer (SMART_DISCH decv) (BACK_PROP decv thmF)
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
            let val thmF = total_time iso_timer thm_of_graph (!graph_glob) in
              total_time degree_timer (SMART_DISCH decv) (BACK_PROP decv thmF)
            end
          val newpath = (undol, decv, colorm, decthm :: thml,g1) :: parentl  
        in
          debug "sat";
          if !iso_flag 
            then graphl := normgraph :: !graphl
            else graphl := mat_copy (!graph_glob) :: !graphl;
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
  

fun sat_solver_wisod size (bluen,redn) isod =
  let
    val _ = init_timer ()
    val _ = isod_glob := isod
    val _ = prop_glob := dempty Int.compare
    val _ = size_glob := size
    val (assignv,clausevv) = init_sat size (bluen,redn)
    val path = [([],0,colorl_glob,[],normalize_nauty_wperm (!graph_glob))]
    val _ = log ("variables: " ^ its (Vector.length assignv))
    val _ = log ("clauses: " ^ its (Vector.length clausevv))
  in
    sat_solver_loop assignv clausevv path
  end

fun sat_solver size (bluen,redn) = 
  sat_solver_wisod size (bluen,redn) (dempty IntInf.compare)

fun sat_solver_edgecl edgecl size (bluen,redn) =
  let
    val _ = init_timer ()
    val _ = isod_glob := dempty IntInf.compare
    val _ = prop_glob := dempty Int.compare
    val _ = size_glob := size
    val (assignv,clausevv) = init_sat_cached size (bluen,redn)
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
    val _ = (log ("variables: " ^ its (Vector.length assignv));
             log ("clauses: " ^ its (Vector.length clausevv)))
  in
    sat_solver_loop assignv clausevv path
  end  
  
fun is_gcterm x = 
  let val oper = fst (strip_comb x) in 
    is_const oper andalso mem (hd_string (fst (dest_const oper))) [#"G",#"C"]
  end
  
fun ELIM_COND size thm = 
  let
    val sub = List.tabulate (size, fn i => {redex = X i, residue = 
      numSyntax.term_of_int i});
    val thm1 = INST sub thm
    fun test x = not (is_gcterm x orelse is_forall x)
    val arithl = filter test (hyp thm1)
    val thm2 = foldl (uncurry DISCH) thm1 arithl
    val thm3 = let open bossLib in SIMP_RULE (bool_ss ++ ARITH_ss) [] thm2 end
  in
    thm3
  end 

(* -------------------------------------------------------------------------
   Intializing gthmd
   ------------------------------------------------------------------------- *)

fun update_gthmd pard (pari: IntInf.int,graphiperml) =
  let 
    val thm = dfind pari pard
    fun g (graphi,perm) = gthmd_glob := dadd graphi (thm,perm) (!gthmd_glob)
  in
    app g graphiperml
  end 

fun init_gthmd pard cover =
  (
  gthmd_glob := dempty IntInf.compare;
  app (update_gthmd pard) cover
  )

(* -------------------------------------------------------------------------
   Intializing conethmd
   ------------------------------------------------------------------------- *)

fun update_conethmd parconethmd (parcone,childl) =
  let 
    val thm = dfind parcone parconethmd
    fun g childcone = conethmd_glob := dadd childcone thm (!conethmd_glob)
  in
    app g childl
  end

fun init_conethmd parconethmd conecover =
  (
  conethmd_glob := dempty (list_compare Int.compare);
  app (update_conethmd parconethmd) conecover
  )

(* -------------------------------------------------------------------------
   Proving that C(n,m,k+1) implies C(n,m,k).
   ------------------------------------------------------------------------- *)

fun LESS_THAN_NEXT size = 
  let 
    val x = ``x:num``
    val tm1 = numSyntax.mk_less (x,numSyntax.term_of_int size)
    val tm2 = numSyntax.mk_less (x,numSyntax.term_of_int (size+1))
    val tm = mk_forall (x, mk_imp (tm1,tm2))
    val thm = Tactical.TAC_PROOF (([],tm), 
                bossLib.simp_tac numLib.arith_ss [])
  in
    thm
  end

fun DISCHL tml thm = foldl (uncurry DISCH) thm (rev tml)

val NOEQSYM = 
  (mesonLib.chatting := 0; PROVE [] ``!x y. x:num <> y ==> y <> x``);

fun ELIM_COND_GRAPH graph finalthm = 
  let
    val tml = (fst o strip_imp_only o snd o strip_forall) 
      (term_of_graph graph)
    val n = mat_size graph
    val lemma = LESS_THAN_NEXT n
    val v = X n
    val vl = List.tabulate (n,X)
    val tn = numSyntax.term_of_int n
    val tn1 = numSyntax.term_of_int (n+1)
    val thminst = INST [{redex = v, residue = tn}] finalthm
    val lemmal = map (fn x => UNDISCH (SPEC x lemma)) vl
    val elim1 = PROVE_HYPL lemmal thminst
    fun f x = UNDISCH (SPECL [x,tn] prim_recTheory.LESS_NOT_EQ)
    val lemmal2 = map f vl
    val lemmal2' = map (MATCH_MP NOEQSYM) lemmal2
    val elim2 = PROVE_HYPL (lemmal2 @ lemmal2') elim1
    val pairvl = subsets_of_size 2 vl
    val lemmal3 = map (fn vl => UNDISCH (SPECL vl NOEQSYM)) pairvl
    val lessthm = Tactical.TAC_PROOF 
      (([],numSyntax.mk_less (tn,tn1)), 
       bossLib.asm_simp_tac numLib.arith_ss []) 
    val elim3 = PROVE_HYPL (lessthm :: lemmal3) elim2
  in
    GENL vl (DISCHL tml elim3)
  end  
  


  
end (* struct *)

(*
PolyML.print_depth 0;
load "sat"; load "enum"; open enum sat aiLib kernel graph nauty;
PolyML.print_depth 10;
val c44l = range (4,18, fn x => mk_both_cdef x (4,4));
val R444_THM = GET_R_THM 4 (4,4);
*)
