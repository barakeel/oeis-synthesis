(* ===================================================================== *)
(* FILE          : ramseyDefScript.sml                                   *)
(* DESCRIPTION   : Ramsey definitions for R35 and R44 graphs             *)
(* AUTHORS       : Thibault Gauthier                                     *)
(* ===================================================================== *)

(* load "ramseySyntax"; load "graph"; *)

open HolKernel boolLib Parse simpLib boolSimps BasicProvers
local open numTheory prim_recTheory SatisfySimps DefnBase in end
open aiLib kernel rconfig ramseySyntax graph gen 

val _ = new_theory "ramseyDef"

(* -------------------------------------------------------------------------
   Definitions for clauses
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
    ()
  end  
 
val _ = log ("Clause definitions for ramsey 3 5 x")  
val _ = kernel.range (5,14, fn x => mk_both_cdef x (3,5))
val _ = log ("Clause definitions for ramsey 4 4 x")
val _ = kernel.range (4,18, fn x => mk_both_cdef x (4,4))

(* -------------------------------------------------------------------------
   Definitions for graphs
   ------------------------------------------------------------------------- *)

fun mk_gdef size (bluen,redn) (i,tm) = 
  let
    val s = "G" ^ its bluen ^ its redn ^ its size ^ "_" ^ its i 
    val v = mk_var (s,``:(num -> num -> bool) -> bool``)
    val eqtm = mk_eq (mk_comb (v,E), tm)
  in
    new_definition (s ^ "_DEF", eqtm)
  end

fun mk_gdef_conj size (bluen,redn) conj = 
  let 
    val s = "G" ^ its bluen ^ its redn ^ its size
    val v = mk_var (s,``:(num -> num -> bool) -> bool``)
    val eqtm = mk_eq (mk_comb (v,E),conj)
  in
    new_definition (s ^ "_DEF",  eqtm)
  end

fun all_graph_def size (bluen,redn) = 
  let 
    val parl = read_par size (bluen,redn)
    val s = its bluen ^ its redn ^ its size
    val ns = its (length parl)
    val _ = log (s ^  ": " ^ ns ^ " covers")
    val terml = map (term_of_graph o unzip_mat) parl
    (* 
    val termll = mk_batch_full 200 terml
    val conjl = map list_mk_conj termll
    val _ = log (s ^  ": " ^ ns ^ " terms")
    val defl = map (mk_gdef size (bluen,redn)) (number_fst 0 conjl)
    val _ = log (s ^  ": " ^ ns ^ " definitions")
    val conj = list_mk_conj (map (lhs o concl o SPEC_ALL) defl)
    *)
    val conjdef = mk_gdef_conj size (bluen,redn) (list_mk_conj terml)
  in
    ()
  end

val _ = log ("Graph definitions for ramsey 3 5 x")
val _ = kernel.range (5,13, fn x => (log (its x); all_graph_def x (3,5)))  
val _ = log ("Graph definitions for ramsey 4 4 x")
val _ = kernel.range (4,17, fn x => (log (its x); all_graph_def x (4,4)))
  

(*
(hd o CONJUNCTS o UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL) 
(DB.fetch "ramseyDef" "G445_DEF");
*)
val _ = log ("Exporting theory: takes a while")
val _ = export_theory()
