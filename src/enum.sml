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


end (* struct *)

(*
PolyML.print_depth 0;
load "enum"; open sat aiLib graph gen enum;
PolyML.print_depth 10;

load "enum"; open enum;
val thm357 = main 7 (3,5);
val thm358 = main 8 (3,5);
val thm359 = main 9 (3,5);
val thm3510 = main 10 (3,5);
val thm3511 = main 11 (3,5);
val thm3512 = main 12 (3,5);
val thm3513 = main 13 (3,5);
val thm3514 = main 14 (3,5);

val thm4411 = main 11 (4,4);
val thm4412 = main 12 (4,4);
(* val thm4413 = main 13 (4,4); *)
val thm4414 = main 14 (4,4);
val thm3511 = main 15 (4,4);
val thm3512 = main 16 (4,4);
val thm3513 = main 17 (4,4);
val thm3514 = main 18 (4,4);

todo: 
  zip the graphs (only unzip when necessary) to use less memory and 
  cache the results of all_leafs when trying to minize an example

*)
