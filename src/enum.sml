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
    val _ = (disable_log := true; iso_flag := true; proof_flag := false)
    val (graphl,t) = add_time (sat_solver size) (bluen,redn);
    val _ = print_endline ("enum " ^ its bluen ^ its redn ^ 
      its size ^ ": " ^ rts_round 4 t)
  in
    graphl
  end

(* -------------------------------------------------------------------------
   Definitions to make terms shorter
   ------------------------------------------------------------------------- *)

fun mk_gdef size (bluen,redn) (i,graphi) = 
  let
    val graph = unzip_mat graphi
    val tm = term_of_graph graph
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
    val defl = map (mk_gdef size (bluen,redn)) (number_fst 0 parl)
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
   Parallel bottom-up enumeration without proof for 
   R,bluen,redn,size graphs.
   ------------------------------------------------------------------------- *)

fun add_vertex (bluen,redn) set graphi =
  let
    val graph = unzip_mat graphi
    val size = mat_size graph + 1
    val _ = (iso_flag := false; debug_flag := false; proof_flag := false)
    val graphl = sat_solver_edgecl (mat_to_edgecl graph) size (bluen,redn)
    val il = map (zip_mat o nauty.normalize_nauty) graphl  
  in
    set := eaddl il (!set)
  end

fun enum_worker br (i,il) = 
  let  
    val set = ref (eempty IntInf.compare) 
    val dir = !smlExecScripts.buildheap_dir ^ "/graphs"
    val file = dir ^ "/" ^ its i
  in
    app (add_vertex br set) il;
    mkDir_err dir;
    writel file (map IntInf.toString (elist (!set)))
  end

fun merge_one set file = 
  set := eaddl (map stinf (readl file)) (!set)

fun merge_graphs dir = 
  let 
    val set = ref (eempty IntInf.compare) 
    val filel = map (fn x => dir ^ "/" ^ x) (listDir dir)
  in
    app (merge_one set) filel; !set
  end  

fun write_iil file (i,il) = writel file (its i :: map infts il)

fun read_iil file =
  let val sl = readl file in
    (string_to_int (hd sl), map stinf (tl sl))
  end

fun write_br file (bluen,redn) = writel file [its bluen, its redn]
fun read_br file = pair_of_list (map string_to_int (readl file))

val enumspec : (int * int, int * IntInf.int list, unit) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "enum.enumspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = enum_worker,
  write_param = write_br,
  read_param = read_br,
  write_arg = write_iil,
  read_arg = read_iil,
  write_result = let fun f _ () = () in f end,
  read_result = let fun f _ = () in f end
  }

fun parallel_extend ncore expname br set =
  let  
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = clean_dir dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val batchl = number_fst 0 (cut_n (3 * ncore) (elist set))
    val _ = clean_dir (selfdir ^ "/parallel_search")
    val _ = smlParallel.parmap_queue_extern ncore enumspec br batchl
  in
    merge_graphs (dir ^ "/graphs")
  end
    
fun serial_extend br set = 
  let val newset = ref (eempty IntInf.compare) in
    Redblackset.app (add_vertex br newset) set; !newset
  end

fun store_enum size (bluen,redn) set =
  let 
    val dir = selfdir ^ "/ramsey_data"
    val enumname = "enum" ^ its bluen ^ its redn ^ its size
    val il = map infts (elist set) 
  in
    mkDir_err dir;
    writel (dir ^ "/" ^ enumname) il;
    print_endline ("Stored: " ^ enumname)
  end
  
fun extend_loop ncore size (br as (bluen,redn)) set = 
  let
    val expname = "R" ^ its bluen ^ its redn ^ its size
    val newset = 
      let val n = Int.min (ncore,elength set) in
        if n <= 1
        then serial_extend br set
        else parallel_extend n expname br set
      end
    val _ = store_enum size br newset
  in
    if elength newset <= 0 then () else 
    extend_loop ncore (size+1) (bluen,redn) newset
  end;
  
fun enum ncore (bluen,redn) = 
  let val set = enew IntInf.compare [zip_mat (Array2.array (1,1,0))] in
    extend_loop ncore 2 (bluen,redn) set
  end
    
end (* struct *)

(*
PolyML.print_depth 0;
load "enum"; open sat aiLib graph gen enum;
PolyML.print_depth 10;

enum 2 (4,4);
enum 2 (3,5);
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
*)
