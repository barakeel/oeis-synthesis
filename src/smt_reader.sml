structure smt_reader :> smt_reader =
struct

open HolKernel Abbrev boolLib aiLib dir kernel sexp progx smt_hol smt_progx
val ERR = mk_HOL_ERR "smt_reader"

type finfo = string * int * bool
type prog = kernel.prog
type progx = progx.progx
type sexp = sexp.sexp

(* --------------------------------------------------------------------------
   Read a SMT file into a program and then re-translate it and 
   compare the results (todo rename file and separate reading programs from
   file from 
   -------------------------------------------------------------------------- *)

fun first_diff l1 l2 = case (l1,l2) of
    ([],[]) => NONE
  | (r,[]) => raise ERR "more in first" (String.concatWith " " r)
  | ([],r) => raise ERR "more in second" (String.concatWith " " r)
  | (a1 :: m1, a2 :: m2) => 
    if a1 = a2 then first_diff m1 m2 else SOME (a1,a2);

fun read_decl_assertl file =
  let 
    val sl = readl (selfdir ^ "/smt/" ^ file)
    val assertl = butlast (filter (String.isPrefix "(assert") sl)
    val decl_aux = filter (fn x => String.isPrefix "(declare-fun" x orelse
                                String.isPrefix "(define-fun" x) sl
    val decl = dict_sort String.compare decl_aux
  in
    (decl,assertl)
  end
  
fun check_no_change file = 
  let
    val (px1,px2) = read_smt_progxpair (selfdir ^ "/smt/" ^ file)
    val (px1',px2') = progpair_to_progxpair (progxpair_to_progpair (px1,px2))
    val _ = if px1 = px1' andalso px2 = px2' then () else 
            raise ERR (human.humanf (progx_to_prog px1)) 
                      (human.humanf (progx_to_prog px2))
    val pxsmall = name_progx ("small", progx_to_progxx px1)
    val pxfast = name_progx ("fast", progx_to_progxx px2)
    val pxxl = mk_fast_set progx_compare_size 
        (all_subnamed pxsmall @ all_subnamed pxfast)
    val tml = List.concat (map pxx_to_hol pxxl)
    val (newdecl,newassertl) = (get_decl tml,get_assertl tml)
    val (decl,assertl) = read_decl_assertl file
    val ro = 
      (
      case first_diff (dict_sort String.compare decl) 
                      (dict_sort String.compare newdecl) of 
        NONE => 
        (case first_diff (dict_sort String.compare assertl)
                         (dict_sort String.compare newassertl) of 
           NONE => NONE 
         | SOME x => SOME (file,x))
      | SOME a => SOME (file,a)
      )    
  in   
    case ro of SOME (file,(a,b)) => raise ERR file (a ^ " <> " ^ b) 
      | NONE => ()
  end

val share_flag = ref false
val imp_flag = ref false
val eq_flag = ref false
val share_n = ref 0

fun retranslate dir file = 
  let
    val _ = mkDir_err dir
    val l0 = read_smt_hol (selfdir ^ "/smt/" ^ file)
    val (px1,px2) = hol_to_progxpair l0
    val (px1',px2') = 
      if !share_flag 
      then progpair_to_progxpair_shared (progxpair_to_progpair (px1,px2))
      else (px1,px2)
    val eql = if !eq_flag 
              then eq_loop (px1',px2') @ eq_compr (px1',px2') @ 
                   eq_loop2_1 (px1',px2') @ eq_loop2_2 (px1',px2')
              else []
    val impl = if !imp_flag
               then eq_loop_imp (px1',px2') @ eq_compr_imp (px1',px2') @ 
                    eq_loop2_imp (px1',px2')
               else []
    val extrasl = map (sexp_to_string o hol_to_smt) (eql @ impl)
  in
    if !share_flag andalso (px1,px2) = (px1',px2') andalso null extrasl 
      then () else
    let
      val pxsmall = name_progx ("small",progx_to_progxx px1')
      val pxfast = name_progx ("fast",progx_to_progxx px2')
      val pxxl = mk_fast_set progx_compare_size 
        (all_subnamed pxsmall @ all_subnamed pxfast)
      val decl = List.concat (map pxx_to_hol pxxl)      
      val (p1,p2) = (progx_to_prog px1, progx_to_prog px2)
      val infol = [";; small program: " ^ human.humanf p1,
                   ";; " ^ gpt_of_prog p1,
                   ";; fast program: " ^ human.humanf p2,
                   ";; " ^ gpt_of_prog p2]
      val logic = ["(set-logic UFNIA)"]
      val cj = [
                "(assert (exists ((c Int)) (and (>= c 0) "^ 
                "(not (= (small c) (fast c))))))", 
                "(check-sat)"
               ]               
    in   
      write_hol_smt (dir ^ "/" ^ file) (infol @ logic) decl 
        (extrasl @ cj)
    end
  end

(* --------------------------------------------------------------------------
   Create a SMT problem with optional induction instances
   -------------------------------------------------------------------------- *)

val header = ["(set-logic UFNIA)"]
val footer = if !skolemize_flag then ["(check-sat)"] else
             ["(assert (exists ((c Int)) (and (>= c 0) "^ 
              "(not (= (small c) (fast c))))))", 
              "(check-sat)"] 


(* conjecture *)
val sk0 = mk_var ("skcj",alpha);
val leqoper = mk_var ("<=",``:'a -> 'a -> bool``);
fun mk_leq (a,b) = list_mk_comb (leqoper, [a,b]); 
val smallv = mk_var ("small",``:'a -> 'a``);
val fastv = mk_var ("fast",``:'a -> 'a``);

val cj_glob = mk_conj (mk_leq (mk_var ("0",alpha),sk0), 
  mk_neg (mk_eq (mk_comb (smallv,sk0), mk_comb (fastv,sk0))));

  
fun create_decl_only pptop =   
  let 
    val (pp as (px1,px2)) = progpair_to_progxpair_shared pptop
    val pxsmall = progx_to_progxx px1
    val pxfast = progx_to_progxx px2
    val pxxl = mk_fast_set progx_compare_size 
        (all_subnamed pxsmall @ all_subnamed pxfast)
    val decl = add_sdecl (List.concat (map pxx_to_hol pxxl))
  in
    decl
  end
  
fun create_decl_only2 pptop =   
  let 
    val (pp as (px1,px2)) = progpair_to_progxpair_shared pptop
    val pxsmall = name_progx ("small",progx_to_progxx px1)
    val pxfast = name_progx ("fast",progx_to_progxx px2)
    val pxxl = mk_fast_set progx_compare_size 
        (all_subnamed pxsmall @ all_subnamed pxfast)
    val decl = add_sdecl (List.concat (map pxx_to_hol pxxl))
  in
    decl
  end   
 
val xvar = mk_var ("x",alpha)
val yvar = mk_var ("y",alpha)
val zvar = mk_var ("z",alpha) 
 
fun rm_forall_once tm = snd (strip_forall tm)

fun rm_forall tm = 
  if is_forall tm then rm_forall_once tm
  else if is_conj tm then
    let val (a,b) = dest_conj tm in mk_conj (rm_forall a, rm_forall b) end
  else if is_neg tm then mk_neg (rm_forall (dest_neg tm))
  else if is_imp tm then 
    let val (a,b) = dest_imp tm in mk_imp (rm_forall a, rm_forall b) end
  else tm;


fun smart_forall vl tm = 
  let 
    val vl1 = free_vars_lr tm 
    val vl2 = filter (fn x => tmem x vl1) vl 
  in
    list_mk_forall (vl2,tm)
  end

fun split_conj tm = 
  let 
    val (vl,body) = strip_forall tm
    val tml = strip_conj body
  in
    map (smart_forall vl) tml
  end
  
val myconv = normalForms.PURE_NNF_CONV THENC normalForms.PRENEX_CONV THENC 
 normalForms.PURE_CNF_CONV  
   
fun skolemize tml =
  let
    val n = ref 0
    fun g tm = 
      if !cnf_flag 
      then 
        let val tm' = 
          (rhs o concl o myconv) tm handle UNCHANGED => tm
        in
          if !split_conj_flag then split_conj tm' else [tm']
        end
      else [tm]
    fun f tm = 
      if not (is_imp_only tm) then [tm] else
      let 
        val sknx = mk_var ("sk" ^ its (!n) ^ "x", alpha)
        val skny = mk_var ("sk" ^ its (!n) ^ "y", alpha)
        val sknz = mk_var ("sk" ^ its (!n) ^ "z", alpha)
        val sub = [{redex = xvar, residue = sknx}, 
                   {redex = yvar, residue = skny},
                   {redex = zvar, residue = sknz}]
        val (a,b) = dest_imp_only tm
        val newa = subst sub (rm_forall a)
        val _ = incr n 
      in
        g (mk_imp (newa,b))
      end
  in
    List.concat (map f tml) @ [cj_glob]
  end;   
   
fun create_decl pptop = 
  let 
    val (pp as (px1,px2)) = progpair_to_progxpair_shared pptop
    val eql = eq_loop pp @ eq_compr pp @ eq_loop2_1 pp @ eq_loop2_2 pp
    val impl = if !noimp_flag then [] else 
      (eq_loop_imp pp @  eq_compr_imp pp @ eq_loop2_imp pp)
    val pxsmall = name_progx ("small",progx_to_progxx px1)
    val pxfast = name_progx ("fast",progx_to_progxx px2)
    val pxxl = mk_fast_set progx_compare_size 
        (all_subnamed pxsmall @ all_subnamed pxfast)
    val decl = add_sdecl (List.concat (map pxx_to_hol pxxl))
  in
    decl @ eql @ impl
  end
  
  
fun skpb_of_pp (pp,tml) =  
  let val decl = create_decl pp in
    skolemize (decl @ tml)
  end;
  
fun write_induct_pb file decl inductl =
  let val tml = 
    if not (!skolemize_flag) andalso not (!cnf_flag) 
    then (decl @ inductl)
    else skolemize (decl @ inductl)
  in
    write_hol_smt file header tml footer
  end
  
  
end (* struct *)

(*
load "smt_reader"; open aiLib kernel smt_reader;
val filel = listDir (selfdir ^ "/smt");
app check_no_change filel;
*)


(*
load "smt_reader"; open aiLib kernel smt_reader;
val filel = listDir (selfdir ^ "/smt");
val dir = selfdir ^ "/smt_semshared";
eq_flag := true;
share_flag := true;
imp_flag := true;
app (retranslate dir) filel;
*)


(*
val l0 = read_smt_hol "smt/A217.smt2";
val (px1,px2) = hol_to_progxpair l0;
val (px1',px2') = 
  progpair_to_progxpair_shared (progxpair_to_progpair (px1,px2));

(px1,px2) = (px1',px2');

val _ = parmap_sl 40 "smt_reader.find_subprog_pairs" filel;
load "exec_memo";
val f = exec_memo.mk_exec_onev (progx_to_prog small);
abstimer := 0;
List.tabulate (10, f o IntInf.fromInt);
val f = exec_memo.mk_exec_onev (progx_to_prog fast);
abstimer := 0;
List.tabulate (10, f o IntInf.fromInt);


val l1 = filter (fn (((a,b,c),d),e) => b <> 0 andalso c) l0;
val l2 = map (fn (((a,b,c),d),e) => ((a,b),e)) l1;
val l3 = map_snd fingerprint l2;
val f = assoc "small" l';
List.tabulate (10, fn x => (dest_fun1 f) (IntInf.fromInt x));
*)


(*
val l0 = read_smt_hol "smt/A14690.smt2";
take indsem and remove non-inductive (e.g. proven by Z3) 
one after adding sharing and equality axioms
*)



