structure glue :> glue =
struct   

open HolKernel Abbrev boolLib aiLib kernel rconfig graph sat gen cone
ramseySyntax minisatProve
val ERR = mk_HOL_ERR "glue"


(* -------------------------------------------------------------------------
   Create diagonal by block matrix and reduce the set of ramsey clauses
   ------------------------------------------------------------------------- *)

fun shift_edgecl x ecl = map (fn ((a,b),c) => ((a + x, b + x),c)) ecl;

fun diag_mat m1 m2 = 
  let
    val ecl1 = mat_to_edgecl m1
    val ecl2 = shift_edgecl (mat_size m1) (mat_to_edgecl m2)
    val m = edgecl_to_mat (mat_size m1 + mat_size m2) (ecl1 @ ecl2)
  in
    m
  end

(* this reduction step will need to be reproduced in the proof *)
fun reduce_clause mat acc clause = case clause of
    [] => SOME (rev acc)
  | (lit as ((i,j),color)) :: m => 
    let val newcolor = mat_sub (mat,i,j) in
      if newcolor = 0 then reduce_clause mat (lit :: acc) m
      else if color = newcolor then reduce_clause mat acc m else NONE
    end;

fun ramsey_clauses_mat (bluen,redn) mat =
  List.mapPartial (reduce_clause mat []) 
    (ramsey_clauses_bare (mat_size mat) (bluen,redn));

fun ramsey_clauses_diagmat (bluen,redn) m1 m2 =
  ramsey_clauses_mat (bluen,redn) (diag_mat m1 m2)

fun mk_ground_var ((i,j),c) = 
  if c = 1 then mk_var ("E_" ^ its i ^ "_" ^ its j,bool)
  else if c = 2 then mk_neg (mk_var ("E_" ^ its i ^ "_" ^ its j,bool))
  else raise ERR "mk_Eijc" "unexpected color";

fun mk_ground_clause clause = list_mk_disj (map mk_ground_var clause)

fun ramsey_clauses_ground (bluen,redn) m1i m2i =
  let val clauses = ramsey_clauses_diagmat (bluen,redn) 
    (unzip_mat m1i) (unzip_mat m2i) 
  in
    map mk_ground_clause clauses
  end
    
(* -------------------------------------------------------------------------
   Add cone clauses
   ------------------------------------------------------------------------- *)

fun mk_cone_clause conel column = 
  let 
    val l1 = map (fn x => combine (column,x)) conel
    val l2 = map (filter (fn (_,c) => c <> 0)) l1
    val l3 = map (fn x => list_mk_conj (map mk_ground_var x)) l2
  in
    list_mk_disj l3
  end
    
fun cone_clauses_ground (bluen,redn) m1i m2i =
  let 
    val conel = map fst (read_cone (bluen,redn) m1i)  
    val size1 = mat_size (unzip_mat m1i)
    val size2  = mat_size (unzip_mat m2i)
    fun mk_column j = List.tabulate (size1,fn i => (i,j+size1))
    val columns = List.tabulate (size2,mk_column)
  in
    map (mk_cone_clause conel) columns 
  end

fun glue_pb cone_flag (bluen,redn) m1i m2i =
  let
    val rclauses = ramsey_clauses_ground (bluen,redn) m1i m2i
    val cclauses = 
      if cone_flag then cone_clauses_ground (bluen,redn) m1i m2i else []
  in
    mk_neg (list_mk_conj (cclauses @ rclauses))
  end
  
fun glue cone_flag (bluen,redn) m1i m2i = 
  SAT_PROVE (glue_pb cone_flag (bluen,redn) m1i m2i)

(* -------------------------------------------------------------------------
   Write gluing scripts
   ------------------------------------------------------------------------- *)

fun write_gluescript dirname 
  cone_flag (b1,r1,size1) (b2,r2,size2) (bluen,redn)    
  (batchi,ipairl) = 
  let 
    val s1 = its b1 ^ its r1 ^ its size1
    val s2 = its b2 ^ its r2 ^ its size2
    val id = s1 ^ "_" ^ s2
    val thyname = "ramseyGlue_" ^ id ^ "_" ^ its batchi
    val filename = selfdir ^ "/" ^ dirname ^ "/" ^ thyname ^ "Script.sml"
    val param = "(" ^ its bluen ^ "," ^ its redn ^ ")"
    val open_cmd = ["open HolKernel boolLib kernel glue"]
    val newtheory_cmd = ["val _ = new_theory " ^ mlquote thyname]
    fun save_cmd (i,(m1i,m2i)) = 
      let 
        val thmname = "RamseyGlue_" ^ id ^ "_" ^ its i 
        val graph1 = "(stinf " ^ mlquote (infts m1i) ^ ")"
        val graph2 = "(stinf " ^ mlquote (infts m2i) ^ ")"
        val bs = bts cone_flag
        val argls = String.concatWith " " [bs,param,graph1,graph2]
      in
        "val _ = save_thm (" ^  mlquote thmname ^ ", glue " ^ argls ^ ")"
      end
    val export_cmd = ["val _ = export_theory ()"]
  in
    writel filename (open_cmd @ newtheory_cmd @
       map save_cmd ipairl @ export_cmd)
  end

fun write_gluescripts dirname batchsize cone_flag 
  (b1,r1,size1) (b2,r2,size2) (bluen,redn) = 
  let
    val _ = mkDir_err (selfdir ^ "/" ^ dirname)
    val parl1 = read_par size1 (b1,r1)
    val _ = print_endline ("parl1: " ^ its (length parl1))
    val parl2 = read_par size2 (b2,r2)
    val _ = print_endline ("parl2: " ^ its (length parl2))
    val pairl = cartesian_product parl1 parl2
    val _ = print_endline ("pairl: " ^ its (length pairl))
    fun difficulty (a,b) = 
      number_of_holes (unzip_mat a) + number_of_holes (unzip_mat b)
    val pairlsc = map_assoc difficulty pairl
    val sortedl = map fst (dict_sort compare_imax pairlsc)
    val ncut = (length sortedl div batchsize) + 1
    val batchl = number_fst 0 (cut_modulo ncut (number_fst 0 sortedl))
  in
    app (write_gluescript dirname cone_flag 
           (b1,r1,size1) (b2,r2,size2) (bluen,redn))
    batchl
  end

end (* struct *)

(*
PolyML.print_depth 0;
load "glue"; load "gen"; open aiLib kernel graph rconfig sat gen glue ramseySyntax;
PolyML.print_depth 10;

write_gluescripts "RamseyGlue" 1 true (4,4,17) (3,5,7) (4,5);
write_gluescripts "RamseyGlue" 1 true (4,4,16) (3,5,8) (4,5);
write_gluescripts "RamseyGlue" 50 true (4,4,15) (3,5,9) (4,5);
write_gluescripts "RamseyGlue" 50 true (4,4,14) (3,5,10) (4,5);


write_gluescripts "RamseyGlueAlt" 50 true (3,5,12) (4,4,12) (4,5);
write_gluescripts "RamseyGlueAlt" 50 true (3,5,13) (4,4,11) (4,5);


*)


(*
PolyML.print_depth 0;
load "glue"; load "gen"; open aiLib kernel graph rconfig sat gen glue ramseySyntax;
PolyML.print_depth 10;

val size44 = 14;
val size35 = 10;
val m4414l = read_par size44 (4,4);
val m3510l = read_par size35 (3,5);
val m44i = hd (read_par size44 (4,4));
val m35i = hd (read_par size35 (3,5));
val tm = glue_pb true (4,5) m44i m35i;

load "minisatProve"; open minisatProve;
val thm = minisatProve tm;
val thm = glue true (4,5) m44i m35i;
*)
