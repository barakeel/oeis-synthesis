(* ========================================================================= *)
(* DESCRIPTION   : Translate between HOL terms and SMT expressions           *)
(* ========================================================================= *)

structure smt_hol :> smt_hol =
struct

open HolKernel Abbrev boolLib aiLib dir kernel sexp
val ERR = mk_HOL_ERR "smt_hol"

type finfo = string * int * bool
type prog = kernel.prog
type progx = progx.progx
type sexp = sexp.sexp

(* --------------------------------------------------------------------------
   Parsing SMT file into S-expressions
   -------------------------------------------------------------------------- *)

fun is_comment line = String.size line >= 2 andalso 
                      String.substring (line, 0, 2) = ";;"     

fun parse_smt_line line =
  if is_comment line then NONE else SOME (string_to_sexp line)

fun read_smt_sexp file = List.mapPartial parse_smt_line (readl file)

(* --------------------------------------------------------------------------
   S-expressions to HOL terms
   -------------------------------------------------------------------------- *)

fun smtv_to_hol v = case v of
    Sexp [Atom x, Atom "Int"] => mk_var (x,alpha)
  | _ => raise ERR "smtv_to_hol" "not supported"
  
fun smtvl_to_hol vl = case vl of
    Sexp l => map smtv_to_hol l
  | _ => raise ERR "smtvl_to_hol" "unexpected";

fun smt_to_hol sexp = case sexp of
    Sexp [Atom "forall", vl, body] => 
    list_mk_forall (smtvl_to_hol vl, smt_to_hol body)
  | Sexp [Atom "exists", vl, body] =>
    list_mk_exists (smtvl_to_hol vl, smt_to_hol body)
  | Sexp [Atom "=", e1, e2] => mk_eq (smt_to_hol e1, smt_to_hol e2)
  | Sexp (Atom a :: el) => 
    list_mk_comb (mk_var (a, rpt_fun_type (length el + 1) alpha), map 
    smt_to_hol el)
  | Atom a => mk_var (a, alpha)
  | _ => raise ERR "smt_to_hol" "not supported";
     
fun get_assert e = case e of
    Sexp [Atom "assert",e'] => SOME e'
  | _ => NONE;

(* --------------------------------------------------------------------------
   Read a file into SMT and HOL formats
   -------------------------------------------------------------------------- *)

val reservedin = ["0","1","2","+","-","*","divf","modf","<=","ite"]

(* recursive functions are exactly those that contains a subfunction *)
fun is_recursive vls def =
  let val (oper,argl) = strip_comb def in
    not (mem (string_of_var oper) (vls @ reservedin)) orelse   
    exists (is_recursive vls) argl
  end;
 
fun add_info tm = 
  let
    val (decl,def) = dest_eq (snd (strip_forall tm)) 
    val narg = length (snd (strip_comb decl))
    val opers = string_of_var (fst (strip_comb decl))
    val vls = map string_of_var (snd (strip_comb decl))
  in
    ((opers,narg,is_recursive vls def),tm)
  end;

fun read_smt_hol file = 
  let
    val l1 = read_smt_sexp file
    val l2 = List.mapPartial get_assert l1
    val l3 = map smt_to_hol (butlast l2)
  in
    map add_info l3
  end

(* --------------------------------------------------------------------------
   HOL terms to S-expressions
   -------------------------------------------------------------------------- *)

fun hol_to_smt_vty v = Sexp [Atom (string_of_var v), Atom "Int"]
fun hol_to_smt_vl vl = Sexp (map hol_to_smt_vty vl)
    
fun hol_to_smt_aux tm = 
  if term_eq tm T then Atom "true"
  else if term_eq tm F then Atom "false"
  else if is_forall tm then   
    let val (vl,body) = strip_forall tm in
      Sexp [Atom "forall", hol_to_smt_vl vl, hol_to_smt_aux body]
    end
  else if is_eq tm then
    let val (a,b) = dest_eq tm in
      Sexp [Atom "=",hol_to_smt_aux a, hol_to_smt_aux b]
    end   
  else if is_conj tm then
    let val (a,b) = dest_conj tm in
      Sexp [Atom "and",hol_to_smt_aux a, hol_to_smt_aux b]
    end
  else if is_disj tm then
    let val (a,b) = dest_disj tm in
      Sexp [Atom "or",hol_to_smt_aux a, hol_to_smt_aux b]
    end
  else if is_neg tm then
    let val a = dest_neg tm in
      Sexp [Atom "not",hol_to_smt_aux a]
    end
  else if is_imp tm then 
    let val (a,b) = dest_imp tm in
      Sexp [Atom "=>",hol_to_smt_aux a, hol_to_smt_aux b]
    end
  else 
    let val (oper,argl) = strip_comb tm in
      if null argl then Atom (string_of_var oper) else
      Sexp (Atom (string_of_var oper) :: map hol_to_smt_aux argl)
    end

fun hol_to_smt tm = Sexp [Atom "assert",hol_to_smt_aux tm]
  handle HOL_ERR _ => raise ERR "hol_to_smt" (term_to_string tm)

fun hol_to_smt_tag (so,tm) = case so of 
    NONE => hol_to_smt tm
  | SOME s => (Sexp [Atom "assert",Sexp 
               [Atom "!", hol_to_smt_aux tm, Atom ":named", Atom s]]
      handle HOL_ERR _ => raise ERR "hol_to_smt_tag" (term_to_string tm))

(* --------------------------------------------------------------------------
   Writing a SMT file from HOL terms
   -------------------------------------------------------------------------- *)

val reservedout = ["0","1","2","+","-","*","<=","ite","x","y","z"]
val reservedout_md = ["0","1","2","+","-","*","<=","ite","x","y","z","modf","divf"]

val divfs = "(define-fun divf ((a Int) (b Int)) Int " ^
            "(ite (= 0 b) 0 (ite (< 0 b) (div a b) (div (- a) (- b))))" ^
            ")"

val modfs = "(define-fun modf ((a Int) (b Int)) Int " ^
            "(ite (= 0 b) 0 (ite (< 0 b) (mod a b) (- (mod (- a) (- b)))))" ^
            ")"

fun declare_var v =
  let 
    val n = arity_of v
    val vs = string_of_var v 
  in
    if vs = "divf" then Atom divfs
    else if vs = "modf" then Atom modfs
    else Sexp [Atom "declare-fun", Atom vs, 
               Sexp (List.tabulate (n,fn _ => Atom "Int")),
               Atom "Int"]
  end

fun get_decl tml = 
  let    
    val vl1 = all_varsl tml
    val vl2 = filter (fn x => not (mem (string_of_var x) reservedout)) vl1
    val vl3 = mk_fast_set Term.compare vl2
  in
    map (sexp_to_string o declare_var) vl3
  end
  
fun get_decl_md tml = 
  let
    val vl1 = all_varsl tml
    val vl2 = filter (fn x => not (mem (string_of_var x) reservedout_md)) vl1
    val vl3 = mk_fast_set Term.compare vl2
  in
    map (sexp_to_string o declare_var) vl3
  end 

fun get_assertl tml = map (sexp_to_string o hol_to_smt) tml

fun write_hol_smt file header tml footer = 
  writel file (header @ get_decl tml @ get_assertl tml @ footer)

(* --------------------------------------------------------------------------
   Writing a SMT file from HOL terms: useful instances
   -------------------------------------------------------------------------- *)

val header = ["(set-logic UFNIA)"]
val footer = ["(check-sat)"]     

fun write_smt file tml = write_hol_smt file header tml footer


end (* struct *)
