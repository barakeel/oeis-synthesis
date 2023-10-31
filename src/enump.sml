structure enump :> enump =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty rconfig sat enum
val ERR = mk_HOL_ERR "enump"

(* -------------------------------------------------------------------------
   Definitions of generalized graphs
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
   Proves that ramsey clauses on bigger graphs imply ramsey clauses
   on smaller graphs
   ------------------------------------------------------------------------- *)

fun Cid size (bluen,redn) b = 
  "C" ^ its bluen ^ its redn ^ its size ^ (if b then "b" else "r")
  
fun C_SMALLER size (bluen,redn) b = 
  let
    val colorn = if b then bluen else redn
    val sbig = Cid (size+1) (bluen,redn) b
    val ssmall = Cid size (bluen,redn) b
    val defbig = DB.fetch "scratch" (sbig ^ "_DEF")
    val defsmall = DB.fetch "scratch" (ssmall ^ "_DEF")
    val f = rhs o snd o strip_forall o concl
    val thm1 = UNDISCH_ALL (SPEC_ALL (ASSUME (f defbig)))
    val lemma = LESS_THAN_NEXT size
    val vl = List.tabulate (colorn,X)
    val lemmal = map (fn x => UNDISCH (SPEC x lemma)) vl
    val thm2 = (foldl (uncurry PROVE_HYP) thm1) lemmal
    val terml = (fst o strip_imp) ((snd o strip_forall) (f defsmall))
    val thm3 = foldl (uncurry DISCH) thm2 (rev terml)
    val thm4 = EQ_MP (SYM (SPEC_ALL defsmall)) (GENL vl thm3)
    val thm5 = PROVE_HYP_EQ (SPEC_ALL defbig) thm4
  in
    thm5
  end

(* -------------------------------------------------------------------------
   Construct Ramsey theorems from Ramsey theorems at smaller sizes
   ------------------------------------------------------------------------- *)

fun R_THM size (bluen,redn) =
  let
    val cover = read_cover size (bluen,redn)
    val pard = create_pard size (bluen,redn) (map fst cover)
    val _ = init_gthmd pard cover
    val _ = (iso_flag := false; debug_flag := false; proof_flag := true)
    val _ = sat_solver size (bluen,redn)
  in
    ELIM_COND size (!final_thm)
  end
  
fun NEXT_R_THM size (bluen,redn) prevthm = 
  let
    val gs = "G" ^ its bluen ^ its redn ^ its (size - 1)
    val prevgenl = map fst (read_cover (size - 1) (bluen,redn))
    val cover = read_cover size (bluen,redn)
    val pard = create_pard size (bluen,redn) (map fst cover)
    val _ = init_gthmd pard cover
    fun f1 mi = 
      let 
        val m = unzip_mat mi
        val _ = (iso_flag := false; debug_flag := false; proof_flag := true)
        val _ = sat_solver_edgecl (mat_to_edgecl m) size (bluen,redn) 
      in
        ELIM_COND_GRAPH m (!final_thm)
      end
    fun f2 i x =  
      let val s = gs ^ "_" ^ its i ^ "_DEF" in
        EQ_MP (SYM (SPEC_ALL (DB.fetch "scratch" s))) x
      end
    val thml0 = map f1 prevgenl (* parallelization point *)
    val thml1 = mapi f2 thml0
    val thm2 = LIST_CONJ thml1;
    val conjdef = DB.fetch "scratch" (gs ^ "_DEF")
    val conjthm = (snd o EQ_IMP_RULE o SPEC_ALL) conjdef
    val thm3 = MP conjthm thm2
    val thm4 = PROVE_HYP thm3 prevthm
    val (thmb,thmr) = 
      (C_SMALLER (size - 1) (bluen,redn) true, 
       C_SMALLER (size - 1) (bluen,redn) false);
  in
    PROVE_HYPL [thmb,thmr] thm4
  end  
  

  
end (* struct *)

(*
PolyML.print_depth 0;
load "enump"; open enum sat aiLib kernel graph nauty sat enum enump;
PolyML.print_depth 10;

rconfig.disable_log := true;
val _ = range (4,18, fn x => mk_both_cdef x (4,4));

val R444_THM = R_THM 4 (4,4);
val R445_THM = NEXT_R_THM 5 (4,4) R444_THM;
val R446_THM = NEXT_R_THM 6 (4,4) R445_THM;
val R447_THM = NEXT_R_THM 7 (4,4) R446_THM;
val R448_THM = time (NEXT_R_THM 8 (4,4)) R447_THM;
val R449_THM = time (NEXT_R_THM 9 (4,4)) R448_THM;
*)
