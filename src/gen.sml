(* =========================================================================
   Compute a set of genralized graphs covering a set of graphs
   ========================================================================= *)
   
structure gen :> gen =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty sat rconfig
  rconfig satenc smlParallel
val ERR = mk_HOL_ERR "gen"

val nauty_time = ref 0.0
val normalize_nauty = total_time nauty_time normalize_nauty

(* -------------------------------------------------------------------------
   Going up and down in the tree
   ------------------------------------------------------------------------- *) 

fun apply_coloring m edgecl = 
   let 
     val newm = mat_copy m
     fun f ((i,j),c) = mat_update_sym (newm,i,j,c) 
   in
     app f edgecl; newm
   end

fun all_coloring edgel = 
  let
    val edgebothl =
      let 
        val l = ref []
        fun f (i,j) = l := [((i,j),blue),((i,j),red)] :: !l 
      in 
        (app f edgel; !l)
      end
  in
    cartesian_productl edgebothl
  end
        
        
fun all_parents m = 
  let
    val l = ref []
    fun f (i,j,x) =
      if x = 0 then () else 
      let 
        val newm = mat_copy m
        val _ = mat_update_sym (newm,i,j,0)
      in 
        l := newm :: !l
      end
  in
    mat_traverse f m; nauty_set (!l)
  end
  
fun all_children m = 
  let
    val l = ref []
    fun f (i,j,x) =
      if x <> 0 then () else 
      let 
        val bluem = mat_copy m
        val _ = mat_update_sym (bluem,i,j,blue)
        val redm = mat_copy m
        val _ = mat_update_sym (redm,i,j,red)
      in 
        l := bluem :: redm :: !l
      end
  in
    mat_traverse f m; nauty_set (!l)
  end 
  
fun random_children_pair m = 
  let 
    val (i,j) = random_elem (all_holes m)
    val bluem = mat_copy m
    val _ = mat_update_sym (bluem,i,j,blue)
    val redm = mat_copy m
    val _ = mat_update_sym (redm,i,j,red)
  in
    [bluem,redm]
  end
  
  
fun all_existing_children set m = 
  let
    val rset = ref (eempty mat_compare)
    fun f (i,j,x) =
      if x <> 0 then () else 
      let 
        val bluem = mat_copy m
        val _ = mat_update_sym (bluem,i,j,blue)
        val normbluem = normalize_nauty bluem
        val redm = mat_copy m
        val _ = mat_update_sym (redm,i,j,red)
        val normredm = normalize_nauty redm
        fun add m = if emem m set then rset := eadd m (!rset) else ()
      in 
        add normbluem; add normredm
      end
  in
    mat_traverse f m; elist (!rset)
  end  

fun all_leafs m =
  let
    val edgel = all_holes m
    val coloringl = all_coloring edgel
    val childl = map (apply_coloring m) coloringl
  in
    nauty_set childl
  end;


fun all_leafs_wperm m =
  let
    val edgel = all_holes m
    val coloringl = all_coloring edgel
    val childl = map (apply_coloring m) coloringl
    val childl_ext = map normalize_nauty_wperm childl
  in
    mk_fast_set (fst_compare mat_compare) childl_ext
  end;



fun all_leafs_wperm_cache cache m =
  let
    val edgel = all_holes m
    val coloringl = all_coloring edgel
    val childl = map (apply_coloring m) coloringl
    fun normalize child = 
      let val childi = zip_mat child in
        dfind childi (!cache) handle NotFound =>
        let 
          val (normm,perm) = normalize_nauty_wperm child 
          val r  = (zip_mat normm,perm)
        in
          cache := dadd childi r (!cache);
          r
        end
      end
    val childl_ext = map normalize childl
  in
    mk_fast_set (fst_compare IntInf.compare) childl_ext
  end


(* -------------------------------------------------------------------------
   Global generalization
   ------------------------------------------------------------------------- *) 


fun all_parents_ramsey (bluen,redn) resultd topm = 
  let
    val bluem = mat_copy topm 
    fun f (i,j,x) = if x = 0 then mat_update_sym (bluem,i,j,blue) else ()
    val _ = mat_traverse f topm
    val redm = mat_copy topm
    fun f (i,j,x) = if x = 0 then mat_update_sym (redm,i,j,red) else ()
    val _ = mat_traverse f topm
    fun f (i,j,x) =
      if x = 0 then () else 
      let 
        val sibcolor = 3 - x
        val sibm = mat_copy (if sibcolor = blue then bluem else redm)
        val _ =  mat_update_sym (sibm,i,j,sibcolor)
      in 
        if is_ramsey_edge (bluen,redn) sibm ((i,j),sibcolor) then
          let 
            val parentm = mat_copy topm
            val _ = mat_update_sym (parentm,i,j,0)
            val normparentm = zip_mat (normalize_nauty parentm)
          in 
            resultd := eadd normparentm (!resultd)
          end
        else ()
      end
  in
    mat_traverse f topm
  end

fun rgeneralize_one (bluen,redn) childl = 
  let
    val resultd = ref (eempty IntInf.compare)
    val parentl = app (all_parents_ramsey (bluen,redn) resultd) childl
  in
    map unzip_mat (elist (!resultd))
  end;

fun all_parents_fair siblingd resultd m = 
  let
    fun f (i,j,x) =
      if x = 0 then () else 
      let 
        val sibm = mat_copy m
        val _ = mat_update_sym (sibm,i,j,3-x)
        val normsibm = zip_mat (normalize_nauty sibm)
      in 
        if emem normsibm siblingd then
          let 
            val parentm = mat_copy m
            val _ = mat_update_sym (parentm,i,j,0)
            val normparentm = zip_mat (normalize_nauty parentm)
          in 
            resultd := eadd normparentm (!resultd)
          end
        else ()
      end
  in
    mat_traverse f m
  end

fun ggeneralize_one childl = 
  let
    fun test m = number_of_blueedges m mod 2 = 0
    val (evenl,oddl) = partition test childl
    val (selectl,siblingd) = 
      if length evenl <= length oddl 
      then (evenl, enew IntInf.compare (map zip_mat oddl))  
      else (oddl, enew IntInf.compare (map zip_mat evenl))
    val resultd = ref (eempty IntInf.compare)
    val parentl = app (all_parents_fair siblingd resultd) selectl
  in
    map unzip_mat (elist (!resultd))
  end;

fun compute_pardescd level leafd childescd childset parentl =
  let
    fun lookup_desc x = dfind x childescd handle NotFound => []
    fun all_desc m = List.concat (map lookup_desc 
      (all_existing_children childset m))
    fun all_desc_extra m = m :: all_desc m
    val extral = dfind (level+1) leafd handle NotFound => [] 
    val extraset = enew mat_compare extral
    val _ = log ("  " ^ its (elength extraset) ^ " extra")
    val parentnotextral = filter (fn x => not (emem x extraset)) parentl
    val parentandextral = 
      map_assoc (mat_set o all_desc) parentnotextral @
      map_assoc (mat_set o all_desc_extra) extral           
  in
    dnew mat_compare parentandextral
  end
  
fun loop_ggen level leafd childescd result = 
  let
    val childl = dkeys childescd
    val childset = enew mat_compare childl
    val (parentl,t) = add_time ggeneralize_one childl
    val _ = log (its (level+1) ^ ": " ^ 
      its (length parentl) ^ " parents in "  ^ 
      rts_round 4 t ^ " seconds")
    val (pardescd,t) = add_time 
      (compute_pardescd level leafd childescd childset) parentl
    val _ = log ("  " ^ its (dlength pardescd) ^ 
      " parents with descendants in " ^ rts_round 4 t ^ " seconds")  
    val childset_small = enew mat_compare 
      (List.concat (map (all_existing_children childset) (dkeys pardescd)))   
    val _ = log ("  " ^ its (elength childset_small) ^ " children")
    val orphanl = filter (fn (x,_) => not (emem x childset_small)) 
      (dlist childescd)
    val newresult = orphanl @ result
    val _ = log ("  " ^ its (length orphanl) ^ " orphans")
    val newleafd = drem level leafd
  in
    if dlength pardescd <= 0 andalso dlength newleafd <= 0 
    then newresult 
    else loop_ggen (level + 1) newleafd pardescd newresult
  end

fun ggeneralize leafl = 
  let 
    val leafd = dregroup Int.compare 
      (map swap (map_assoc number_of_holes leafl))
    val minlevel = list_imin (dkeys leafd) 
    val extral = dfind minlevel leafd
    val _ = log ("  " ^ its (length extral) ^ " extra")
    val childescd = dnew mat_compare (map (fn x => (x,[x])) extral)
    val orphanl = loop_ggen minlevel leafd childescd []
    val leafset1 = dict_sort mat_compare leafl
    val leafset2 = mk_fast_set mat_compare (List.concat (map snd orphanl))
    val _ = log "Verifying that all leafs are covered"
    val _ = 
      if list_compare mat_compare (leafset1,leafset2) <> EQUAL
      then raise ERR "ggeneralize" 
        (its (length leafset1) ^ " <> " ^ its (length leafset2))
      else ()
  in
    orphanl
  end
  


(* -------------------------------------------------------------------------
   Faster generalization (from a set of leafs)
   ------------------------------------------------------------------------- *) 

fun abstractable_edgel leafd m l = 
  let
    val sibm = mat_copy m 
    fun f (i,j) = mat_update_sym (sibm,i,j, 3 - mat_sub(m,i,j))
    val _ = app f l
  in
    emem (normalize_nauty sibm) leafd
  end;

fun add_edge edgell aedgel1 = 
  let 
    val l1 = cartesian_product edgell aedgel1
    fun f (a,b) = 
      let 
        val set0 = List.concat [a,b]
        val set1 = mk_fast_set edge_compare set0
      in
        if length set0 = length set1 then SOME set1 else NONE
      end
  in
    mk_fast_set (list_compare edge_compare) (List.mapPartial f l1)
  end;

fun test_edgel set edgel = 
  let 
    val subsets = subsets_of_size (length edgel - 1) edgel 
    fun test subset = emem (dict_sort edge_compare subset) set
  in
    all test subsets
  end;
 
fun fgen_loop (leafd,aedgel1,m) aedgel result =
  let 
    fun f () =
      let val set = enew (list_compare edge_compare) aedgel
          val oedgel = add_edge aedgel aedgel1
          val tedgel = filter (test_edgel set) oedgel;
          val newaedgel = filter (abstractable_edgel leafd m) tedgel
      in
        newaedgel
      end
    val (newaedgel,t) = add_time f ()
    val _ = log (its (length newaedgel) ^ " in " ^ rts_round 4 t ^ " seconds")
  in
    if null newaedgel then result else
    fgen_loop (leafd,aedgel1,m) newaedgel (newaedgel :: result)
  end;

fun fgeneralize leafd m =
  let 
    val tedgel = map (fn (x,_) => [x]) (mat_to_edgecl m)
    val aedgel1 = filter (abstractable_edgel leafd m) tedgel
    fun mk_parent m edgel = 
      let
        val parm = mat_copy m 
        fun f (i,j) = mat_update_sym (parm,i,j,0)
      in
        app f edgel; parm
      end
    fun mk_parentl m edgell = nauty_set (map (mk_parent m) edgell)
    val r = fgen_loop (leafd,aedgel1,m) aedgel1 [aedgel1]
  in
    map (mk_parentl m) r
  end;


(*
PolyML.print_depth 0;
load "gen"; load "ramsey"; open ramsey kernel aiLib gen graph;
PolyML.print_depth 10;

val leafl = map unzip_mat (read35 10); length leafl; 
val leafd = enew mat_compare leafl;
val (cover,covered) = split (compute_cover leafl);
length cover; map length covered;

val leafl = map unzip_mat (read44 10); length leafl; 
val leafd = enew mat_compare leafl;
fgen_flag := true;
val (cover44,covered44) = split (compute_cover leafl);
length cover44; map length covered44;
*)

(* -------------------------------------------------------------------------
   Generalization (from a set of leafs)
   ------------------------------------------------------------------------- *) 

val gen_width = ref 100  
val gen_depth = ref 100


fun next_gen leafd l = 
  let  
    val childset = enew mat_compare l
    val l1 = mat_set (List.concat (map all_parents l))
    fun is_fullanc m = all (fn x => emem x leafd) (all_leafs m)
    val l2 = filter is_fullanc l1;
  in
    (* random_subset (!gen_width) *) l2
  end;

fun loop_gen ngen leafd l result =
  let
    val (nextl,t) = add_time (next_gen leafd) l
    val _ = log (its (ngen+1) ^ ": " ^ 
      its (length nextl) ^ " in " ^ rts_round 4 t ^ " seconds")
  in
    if null nextl then rev result else 
    loop_gen (ngen + 1) leafd nextl (l :: result)
  end;
  
fun generalize leafd leaf = loop_gen 0 leafd [leaf] []

(* -------------------------------------------------------------------------
   Computing best cover
   ------------------------------------------------------------------------- *) 

val fgen_flag = ref false

fun cover_score coverd mp =
  length (filter (fn x => not (emem x coverd)) (all_leafs mp))

fun find_best_mpl coverd mpl =
  hd (dict_sort compare_imax (map_assoc (cover_score coverd) mpl))

fun find_best_mpll coverd mpll = 
  let 
    val l1 = map (find_best_mpl coverd) mpll 
    val l2 = map_snd (fn x => ~x) l1
    val l3 = number_snd 0 l2
    val l4 = map (fn ((a,b),c) => (a,(b,c))) l3
    val cmp = snd_compare (cpl_compare Int.compare Int.compare)
  in
    hd (dict_sort cmp l4)
  end  
  
fun loop_cover leafs leafd coverd uncover result =
  if null uncover then rev result else
  let 
    val m0 = random_elem uncover    
    val (mpll,t1) = 
       if !fgen_flag 
       then add_time (fgeneralize leafd) m0
       else add_time (generalize leafd) m0
    val ((mp,(sc,depth)),t2) = add_time (find_best_mpll coverd) mpll
    val mcover = filter (fn x => not (emem x coverd)) (all_leafs mp) 
    val mcoverd = enew mat_compare mcover
    val newcoverd = eaddl mcover coverd
    val newuncover = filter (fn x => not (emem x mcoverd)) uncover
    val _ = log (
      "Covering " ^ its (~sc) ^ " graphs (" ^ 
      its (length newuncover) ^ " remaining)" ^
      " at depth " ^ its (length mpll - 1) ^ "," ^ its depth ^ 
      " in " ^ rts_round 4 t1 ^ " seconds and in " ^ 
      rts_round 4 t2 ^ " seconds")
  in  
    loop_cover leafs leafd newcoverd newuncover ((mp,mcover) :: result)
  end;
  
fun compute_cover leafs = 
  let val leafd = enew mat_compare leafs in 
    loop_cover leafs leafd (eempty mat_compare) leafs [] 
  end

(* -------------------------------------------------------------------------
   Fast cover
   ------------------------------------------------------------------------- *)

fun enc_color (x,c) = if c = 1 then 2 * x else 2 * x + 1;
fun enc_edgec (e,c) = enc_color (edge_to_var e,c);
fun dec_edgec x = (var_to_edge (x div 2), (x mod 2) + 1);
fun opposite (e,x) = (e,3 - x)

fun init_sgen size (bluen,redn) = 
  let
    val clauses1 = sat.ramsey_clauses size (bluen,redn)
    val clauses2 = map (map enc_color) clauses1
    val clausev = Vector.fromList clauses2;
    val claused = dnew (list_compare Int.compare) (number_snd 0 clauses2)
    fun g clause = map_assoc (fn _ => clause) clause
    val clauses3 = List.concat (map g clauses2)
    val clauses4 = dlist (dregroup Int.compare clauses3)
    val clauses5 = map_snd (map (fn x => dfind x claused)) clauses4
    val clauses6 = map_snd (dict_sort Int.compare) clauses5
    val varv = Vector.fromList (map snd clauses6)
  in
    (varv,clausev)
  end;
  
fun sgeneralize size (bluen,redn) leaf =
  let
    val (varv,clausev) = init_sgen size (bluen,redn) 
    val sizev = Vector.map (fn x => length x - 1) clausev
    val inita = Array.array (Vector.length clausev,0)    
    fun update_numbera a v = 
      let 
        val il = Vector.sub (varv,v) 
        fun g i = Array.update (a,i, Array.sub(a,i) + 1) 
      in
        app g il
      end
    val edgecl = mat_to_edgecl leaf
    val _ = app (update_numbera inita) (map enc_edgec edgecl)
    fun try () = 
      let
        val locala = Array.tabulate 
          (Array.length inita, fn i => Array.sub (inita,i))
        val vlopp = shuffle (map (enc_edgec o opposite) edgecl)
        fun test v = 
          let val clausel = Vector.sub (varv,v) in
            all (fn x => Array.sub (locala, x) < Vector.sub(sizev,x)) clausel
          end
        fun sgen_loop vl result = case filter test vl of
            [] => rev result
          | v :: rem => (update_numbera locala v; sgen_loop rem (v :: result))
      in
        map (fst o dec_edgec) (sgen_loop vlopp [])
      end
    val edgell = List.tabulate (1000,fn _ => try ())  
  in  
    fst (hd (dict_sort compare_imax (map_assoc length edgell)))
  end;


fun build_parent leaf edgel = 
  let
    val parent = mat_copy leaf
    fun f (i,j) = mat_update_sym (parent,i,j,0)
    val _ = app f edgel
  in
    parent
  end;

fun minimize_parent_aux cache uset (parent,parentleafs) = 
  if number_of_holes parent <= 0 then (parent,parentleafs) else
  let 
    fun score uset leafs = 
      length (filter (fn x => emem x uset) (map fst leafs))
    val parentsc = score uset parentleafs
    fun search childl = case childl of [] => NONE | child :: m =>
      let val childleafs = all_leafs_wperm_cache cache child in
        if score uset childleafs >= parentsc
        then SOME (child,childleafs)
        else search m
      end
  in
    case search (all_children parent) of
      NONE => (parent,parentleafs)
    | SOME x => minimize_parent_aux cache uset x
  end;

fun minimize_parent uset parent =
  let 
    val cache = ref (dempty IntInf.compare) 
    val parentleafs = all_leafs_wperm_cache cache parent  
  in
    minimize_parent_aux cache uset (parent,parentleafs)
  end
  
fun loop_scover (bluen,redn) uset result =
  if elength uset <= 0 then rev result else
  let
    val leaf = unzip_mat (random_elem (elist uset))   
    val (edgel,t1) = add_time (sgeneralize (mat_size leaf) (bluen,redn)) leaf
    val parent = build_parent leaf edgel
    val ((minparent,parentleafs),t2) = add_time (minimize_parent uset) parent
    val pcover = filter (fn x => emem (fst x) uset) parentleafs
    val newuset = ereml (map fst pcover) uset
    val _ = log (
      "Covering " ^ its (length pcover) ^ " graphs (" ^ 
      its (elength newuset) ^ " remaining)" ^
      " at depth " ^ its (number_of_holes parent) ^ 
      "," ^ its (number_of_holes minparent) ^ 
      " in " ^ rts_round 4 t1 ^ " seconds and in " ^ 
      rts_round 4 t2 ^ " seconds")
  in  
    loop_scover (bluen,redn) newuset ((zip_mat minparent,pcover) :: result)
  end;

fun compute_scover (bluen,redn) leafl = 
  let val uset = enew IntInf.compare (map zip_mat leafl) in
    loop_scover (bluen,redn) uset []
  end

(* -------------------------------------------------------------------------
   Parallel version of scover 
   (dropping half of the candidates or more)
   minimization expensive happens inside the threads
   ------------------------------------------------------------------------- *)


fun sgen_worker ((bluen,redn),uset) mati =
  let
    val leaf = unzip_mat mati
    val edgel = sgeneralize (mat_size leaf) (bluen,redn) leaf
    val parent = build_parent leaf edgel
    val (minparent,parentleafs) = minimize_parent uset parent
    val pcover = filter (fn x => emem (fst x) uset) parentleafs
  in
    (zip_mat minparent, pcover)
  end

fun write_infset file ((a,b),set) = writel file 
  (its a :: its b :: map infts (elist set))
fun read_infset file = case readl file of
  sa :: sb :: m => ((string_to_int sa,string_to_int sb), 
                    enew IntInf.compare (map stinf m))
  | _ => raise ERR "read_infset" ""
 
fun write_inf file i = writel file [infts i]
fun read_inf file = stinf (singleton_of_list (readl file))

fun write_par file (p,cperml) = 
  let 
    val ps = infts p
    fun f (c,perm) = infts c ^ " " ^ ilts perm
  in
    writel file (ps :: map f cperml)
  end

fun read_par file = 
  let 
    val sl = readl file
    fun f s = 
      let val sl' = String.tokens Char.isSpace s in
        (stinf (hd sl'), map string_to_int (tl sl'))
      end
  in
    (stinf (hd sl), map f (tl sl))
  end
  

val genspec : ((int * int) * IntInf.int Redblackset.set, IntInf.int, 
  IntInf.int * (IntInf.int * int list) list) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "gen.genspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = sgen_worker,
  write_param = write_infset,
  read_param = read_infset,
  write_arg = write_inf,
  read_arg = read_inf,
  write_result = write_par,
  read_result = read_par
  }


fun update_uset norg ncur pdl (uset,result) =
  if null pdl orelse ncur <= norg div 2 then (uset,result) else
  let 
    val l1 = map_assoc (dlength o snd) pdl
    val l2 = dict_sort compare_imax l1
    val (bestp,bestd) = fst (hd l2)
    val keyl = dkeys bestd
    val newuset = ereml keyl uset
    val newresult = (bestp, dlist bestd) :: result 
    fun test (p,d) = if p = bestp then NONE else 
      let val d' = dreml keyl d in 
        if dlength d' <= 0 then NONE else SOME (p,d')
      end
    val newpdl = List.mapPartial test pdl 
    val _ = log ("Covering " ^ its (dlength bestd) ^ " graphs (" ^ 
                 its (elength newuset) ^ " remaining)" ^
                 " at depth " ^ its (number_of_holes (unzip_mat bestp)))
  in
    update_uset norg (ncur - 1) newpdl (newuset,newresult)
  end

fun loop_scover_para ncore (bluen,redn) uset result = 
  if elength uset <= 0 then rev result else
  let
    val n = Int.min (ncore * 4, elength uset)
    val ul = random_subset n (elist uset)
    val (pl,t) = add_time 
      (smlParallel.parmap_queue_extern (Int.min (n,ncore))
        genspec ((bluen,redn),uset)) ul  
    val pdl = map_snd (dnew IntInf.compare) pl
    val norg = length pdl
    val (newuset,newresult) = update_uset norg norg pdl (uset,result)
  in
    loop_scover_para ncore (bluen,redn) newuset newresult
  end

fun compute_scover_para ncore (bluen,redn) uset = 
  let
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000)
  in
    loop_scover_para ncore (bluen,redn) uset []
  end 

fun store_cover size (bluen,redn) cover = 
  let 
    val dir = selfdir ^ "/ramsey_data";
    val file = dir ^ "/cover" ^ its bluen ^ its redn ^ its size;
    fun f (p,cperml) = 
      let fun g (c,perm) = infts c ^ "_" ^ 
        String.concatWith "_" (map its perm) 
      in
        String.concatWith " " (infts p :: map g cperml)
      end
  in
    mkDir_err dir;
    writel file (map f cover)
  end  

fun all_cover ncore (bluen,redn) (minsize,maxsize) =  
  let
    fun f size =
      let
        val _ = print_endline ("SIZE " ^ its size) 
        val filein = (selfdir ^ 
          "/ramsey_" ^ its bluen ^ "_" ^ its redn ^ "/" ^ its size)
        val uset = enew IntInf.compare (map stinf (readl filein));
        val (cover,t) = add_time (compute_scover_para ncore (bluen,redn)) uset
      in
        store_cover size (bluen,redn) cover
      end  
  in
    ignore (range (minsize,maxsize,f))
  end
  
(*
load "gen"; open aiLib kernel gen;
val (_,t) = add_time (all_cover 2 (4,4)) (4,17);
*)

(* -------------------------------------------------------------------------
   Cone generalization
   ------------------------------------------------------------------------- *)

val cone_compare = list_compare Int.compare
val cone_set = mk_fast_set cone_compare   

fun parents cl = case cl of 
    [] => []
  | a :: m => 
      if a <> 0 
      then (0 :: m) :: map (fn x => a :: x) (parents m)
      else map (fn x => a :: x) (parents m)
  
fun instances cl = 
  let val cl' =  map (fn x => if x = 0 then [1,2] else [x]) cl in 
    cartesian_productl cl'
  end
  
fun cnext cset childl = 
  let  
    val childset = enew (list_compare Int.compare) childl
    val l1 = cone_set (List.concat (map parents childl))
    fun is_fullanc m = all (fn x => emem x cset) (instances m)
    val l2 = filter is_fullanc l1
  in
    (* random_subset (!gen_width) *) l2
  end;

fun cloop cset childl =
  let val parentl = cnext cset childl
  in
    if null parentl
    then (random_elem childl)
    else cloop cset parentl
  end;
  
fun cgeneralize cset leaf = cloop cset [leaf];
  
fun n_hole cl = length (filter (fn x => x = 0) cl);  
  
fun ccover_loop uset = 
  if elength uset <= 0 then [] else 
  let 
    val (parentl,t) = add_time (map (cgeneralize uset)) (elist uset)
    val parentlsc = map_assoc n_hole parentl
    val (parent,sc) = hd (dict_sort compare_imax parentlsc)
    val leafs = instances parent
    val newuset = ereml leafs uset
    val _ = log (its (elength newuset) ^ " " ^ rts_round 2 t)
  in
    parent :: ccover_loop newuset
  end
      
fun ccover conel = ccover_loop (enew cone_compare conel)

end (* struct *)

(*
load "gen"; open gen sat;

(* creating all cones *)
PolyML.print_depth 0;
load "ramsey"; load "gen"; load "sat"; 
open ramsey aiLib kernel graph sat nauty gen rconfig;
PolyML.print_depth 10;

val size = 14;
val m = unzip_mat (random_elem (read44 size));
val matl = sat_solver_edgecl (mat_to_edgecl m) (size+1) (4,5);
fun pairbelowy y = List.tabulate (y,fn x => (x,y));
val edgel = pairbelowy size;
fun mat_to_list mx = map (fn (x,y) => mat_sub (mx,x,y)) edgel; 
val cl = map mat_to_list matl;
val cset =  cl;
val cover = ccover cset;
writel ("ramsey_cone/" ^ szip_mat m) (map ilts cover);



fun switch_color m = mat_tabulate (mat_size m, fn (i,j) => 
  if mat_sub (m,i,j) = 0 then 0 else 3 - mat_sub (m,i,j));

val m449 = unzip_mat (random_elem (read44 9));
val m3510 = unzip_mat (random_elem (read35 10));
val m4410 = unzip_mat (random_elem (read44 10));
val m5311 = switch_color (unzip_mat (random_elem (read35 11)));

*)




