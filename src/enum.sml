structure enum :> enum =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty rconfig sat gen
val ERR = mk_HOL_ERR "enum"

fun debug_mat m = if !debug_flag then graph.print_mat m else ()


(* -------------------------------------------------------------------------
   First enumeration without proof
   ------------------------------------------------------------------------- *)

fun enum size (bluen,redn) = 
  let
    val _ = (iso_flag := true; proof_flag := false)
    val (graphl,t) = add_time (sat_solver size) (bluen,redn);
    val _ = print_endline ("enum " ^ its bluen ^ its redn ^ 
      its size ^ ": " ^ rts_round 4 t)
  in
    graphl
  end

(* -------------------------------------------------------------------------
   Term
   ------------------------------------------------------------------------- *)
   
fun mk_domain vl size =
  let
    fun f v = numSyntax.mk_less (v,numSyntax.term_of_int size)
    val boundl = map f vl
    val pairvl = map pair_of_list (kernel.subsets_of_size 2 vl)
    val diffl = map (fn (a,b) => mk_neg (mk_eq (a,b))) pairvl
  in
    list_mk_imp (boundl @ diffl,F)
  end
  
fun term_of_graph vl domain graph = 
  let 
    val edgecl = mat_to_edgecl graph
    val litl = map hlit (map_fst edge_to_var edgecl)
  in
    list_mk_forall (vl, list_mk_imp (litl,domain)) 
  end

(* -------------------------------------------------------------------------
   Definitions to make terms shorter
   ------------------------------------------------------------------------- *)

fun mk_gdefi size (bluen,redn) vl domain i graphi = 
  let
    val graph = unzip_mat graphi
    val tm = term_of_graph vl domain graph
    val s = "G" ^ its bluen ^ its redn ^ its size ^ "_" ^ its i 
    val v = mk_var (s,``:(num -> num -> bool) -> bool``)
    val eqtm = mk_eq (mk_comb (v,E), tm)
  in
    new_definition (s ^ "_DEF", eqtm)
  end

fun mk_conjdef size (bluen,redn) conj = 
  let 
    val s = "G" ^ its bluen ^ its redn ^ its size
    val v = mk_var (s,``:(num -> num -> bool) -> bool``)
    val eqtm = mk_eq (mk_comb (v,E),conj)
  in
    new_definition (s ^ "_DEF",  eqtm)
  end

fun create_pard size (bluen,redn) parl = 
  if null parl then dempty IntInf.compare else
  let
    val vl = List.tabulate (size, X)
    val domain = mk_domain vl size
    val defl = mapi (mk_gdefi size (bluen,redn) vl domain) parl
    val conj = list_mk_conj (map (lhs o concl o SPEC_ALL) defl)
    val conjdef = mk_conjdef size (bluen,redn) conj
    val f = UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL
    val thml = CONJUNCTS (f conjdef)
    val thml2 = combine (thml, map SPEC_ALL defl)
    val thml3 = map (fn (a,b) => EQ_MP b a) thml2
    val thml4 = map (UNDISCH_ALL o SPEC_ALL) thml3
    val gthml = combine (parl,thml4)
  in
    dnew IntInf.compare gthml
  end

(* -------------------------------------------------------------------------
   Enumeration with proof
   ------------------------------------------------------------------------- *)

fun update_isod_one ((graphi,perm),thm) = 
  case dfindo graphi (!isod_glob) of
    NONE => isod_glob := dadd graphi (thm,perm) (!isod_glob)
  | SOME _ => raise ERR "save_normgraph" ""

fun update_isod pard (pari,graphiperml) =
  let fun g (graphi,perm) = 
    let val thm = dfind pari pard in
      update_isod_one ((graphi,perm),thm)
    end
  in
    app g graphiperml
  end

fun enum_proof size (bluen,redn) pard coverl =
  let 
    val _ = isod_glob := dempty IntInf.compare;
    val _ = app (update_isod pard) coverl
    val _ = (iso_flag := true; proof_flag := true)
    val (satl,t) = add_time (sat_solver_wisod size (bluen,redn)) (!isod_glob)
    val _ = print_endline ("enum_proof " ^ its bluen ^ its redn ^ 
      its size ^ ": " ^ rts_round 4 t)
  in
    ELIM_COND size (!final_thm)
  end
    
fun main size (bluen,redn) = 
  let
    val graphl = enum size (bluen,redn)
    val coverl = compute_scover (bluen,redn) graphl
    val parl = map fst coverl
    val pard = create_pard size (bluen,redn) parl
  in
    enum_proof size (bluen,redn) pard coverl 
  end

(* -------------------------------------------------------------------------
   Parallel bottom-up enumeration without proof for R,4,4,k graphs
   ------------------------------------------------------------------------- *)

fun add_vertex44 set graphi =
  let 
    val _ = hide_stats := true
    val graph = unzip_mat graphi
    val size = mat_size graph + 1
    val graphl = sat_solver_edgecl (mat_to_edgecl graph) size (4,4)
    val il = map (zip_mat o nauty.normalize_nauty) graphl  
  in
    set := eaddl il (!set)
  end

fun worker44 (i,il) = 
  let  
    val set = ref (eempty IntInf.compare) 
    val dir = !smlExecScripts.buildheap_dir ^ "/graphs"
    val file = dir ^ "/" ^ its i
  in
    app (add_vertex44 set) il;
    mkDir_err dir;
    writel file (map IntInf.toString (elist (!set)))
  end

fun merge_one set file = 
  let 
    val sl = readl file
    val il = map stinf sl 
  in
    set := eaddl il (!set)
  end
    
fun merge_graphs dir = 
  let 
    val set = ref (eempty IntInf.compare) 
    val filel = map (fn x => dir ^ "/" ^ x) (listDir dir)
  in
    app (merge_one set) filel; !set
  end  

fun write_iil file (i,il) =
  writel file (its i :: map infts il)

fun read_iil file =
  let 
    val sl = readl file   
    val i = string_to_int (hd sl)
    val il = map stinf (tl sl)
  in 
    (i,il)
  end

val enumspec : (unit, (int * IntInf.int list), unit) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "enum.enumspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = let fun f () x = worker44 x in f end,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_iil,
  read_arg = read_iil,
  write_result = let fun f _ () = () in f end,
  read_result = let fun f _ = () in f end
  }

fun parallel_extend ncore expname set =
  let  
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = mkDir_err dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val batchl = number_fst 0 (cut_n (3 * ncore) (elist set))
    val (_,t) = add_time 
       (smlParallel.parmap_queue_extern ncore enumspec ()) graphill
  in
    merge_graphs (dir ^ "/graphs")
  end
    
fun extend set = 
  let
    val newset = ref (eempty IntInf.compare)
    val ((),t) = add_time (Redblackset.app (add_vertex44 newset)) set   
  in
    !newset
  end
  
fun loop44 ncore i set = 
  let
    val expname = "R44" ^ its (i+1)
    val newset =
      if ncore <= 1 orelse elength set <= 1000 
      then extend set 
      else parallel_extend ncore expname set
    val _ = mkDir_err (selfdir ^ "/ramsey_4_4")
    val il = map infts (elist newset)
    val _ = writel (selfdir ^ "/ramsey_4_4/" ^ its (i+1)) il
  in
    if elength newset <= 0 then () else loop44 ncore (i+1) newset
  end;
  
fun start44 ncore = 
  let val set = enew IntInf.compare [zip_mat (Array2.array (1,1,0))] in
    loop44 ncore 1 set
  end
    
end (* struct *)

(*
PolyML.print_depth 0;
load "enum"; open sat aiLib graph gen enum;
PolyML.print_depth 10;

start44 60;
*)

    

(*

val ramsey_3_5_7 = main 7 (3,5);
val ramsey_3_5_8 = main 8 (3,5);
val ramsey_3_5_9 = main 9 (3,5);
val ramsey_3_5_10 = main 10 (3,5);
val ramsey_3_5_11 = main 11 (3,5);
val ramsey_3_5_12 = main 12 (3,5);
val ramsey_3_5_13 = main 13 (3,5);
val ramsey_3_5_14 = main 14 (3,5);

load "enum"; open enum;
new_theory "ramsey_4_4_11";
val thm4411 = main 11 (4,4);
val ramsey_4_4_11 = save_thm ("ramsey_4_4_11",thm4411);
export_theory ();

load "enum"; open enum;
new_theory "ramsey_4_4_12";
val thm4412 = main 12 (4,4);
val ramsey_4_4_12 = save_thm ("ramsey_4_4_12",thm4412);
export_theory ();

load "enum"; open enum;

fun gen_theory44 size = 
  let 
    val id = "ramsey_4_4_" ^ int_to_string size
    val _ = new_theory id;
    val thm = main size (4,4);
    val _ = save_thm (id,thm);
  in
    export_theory ()
  end;
  
gen_theory44 18;  


val thm4412 = main 12 (4,4);
(* val thm4413 = main 13 (4,4); *)
val thm4414 = main 14 (4,4);
val thm3511 = main 15 (4,4);
val thm3512 = main 16 (4,4);
val thm3513 = main 17 (4,4);
val thm3514 = main 18 (4,4);

*)
