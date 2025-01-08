structure search_term :> search_term =
struct

open HolKernel boolLib aiLib kernel progx smt_hol smt_progx smt_reader kolmo
val ERR = mk_HOL_ERR "searchnew"

type ppsisl = string * string list
exception Parse;

(*
load "search_term"; open kernel aiLib progx smt_progx smt_reader search_term;

debug_flag := false;
ignore_errors := false;
val l = read_inductl "tmt66_3b4";
val l1 = map subz l;
write_inductl "tmt66_3b4_subz" l1;
val l2 = read_inductl "tmt66_3b4_subz";
inductl_cmp (l1,l2);

1) test if the new code works 
   (trying to reprove the new current file)
   extract gpt examples from the current file
   
sh reprove.sh   
   
2) make the subz_flag effective 
   (at creating variants)
3) make a flag for more careful comparisons of induction predicate list

*)

(* -------------------------------------------------------------------------
   Add one variant replacing the y variable by the z variable
   ------------------------------------------------------------------------- *)

val zvar = ``z:'a``;
val yvar = ``y:'a``;
fun is_yvar x = term_eq x yvar;
fun contain_y tm = 
  let val (oper,argl) = strip_comb tm in
    is_yvar oper orelse exists contain_y argl
  end;
 
fun is_zvar x = term_eq x zvar;  
fun contain_z tm = 
  let val (oper,argl) = strip_comb tm in
    is_zvar oper orelse exists contain_z argl
  end;  

fun sub_y_z_one tm = 
  if contain_y tm 
  then [tm, subst [{redex = yvar, residue = zvar}] tm]
  else [tm]

fun sub_y_z tml = List.concat (map sub_y_z_one tml)
  
(* -------------------------------------------------------------------------
   Add two variants randomly expanding definitions
   ------------------------------------------------------------------------- *)

fun beta_reduce x = (rhs o concl o REDEPTH_CONV BETA_CONV) x 
  handle UNCHANGED => x;

fun random_expand d tm =
  let val vl = filter (fn x => dmem x d) (free_vars tm) in
    if null vl then NONE else
    let 
      val v = random_elem vl
      val sub = dfind v d
    in
      SOME (beta_reduce (subst sub tm))
    end
  end;

fun random_expand_twice d tm = case (random_expand d tm) of 
    NONE => NONE
  | SOME newtm => random_expand d newtm

fun expand_def_one d tm = 
  let
    val tm1o = random_expand d tm
    val tm2o = random_expand_twice d tm
  in
    tm :: List.mapPartial I [tm1o,tm2o]
  end
 
fun eq_to_sub tm = 
  let 
    val (a,b) = dest_eq (snd (strip_forall tm))
    val (oper,argl) = strip_comb a
  in
    [{redex = oper, residue = list_mk_abs (argl,b)}]
  end;

fun expand_def pp tml = 
  let 
    val decl = create_decl_only pp 
    val subl = map eq_to_sub decl
    val d = dnew Term.compare (map swap (map_assoc (#redex o hd) subl));
  in
    List.concat (map (expand_def_one d) tml)
  end
  
fun subz (pp,tml) = (pp, expand_def pp (sub_y_z tml))

(* -------------------------------------------------------------------------
   Global parameters from config file
   ------------------------------------------------------------------------- *)

val ncore = string_to_int (dfind "ncore" configd) handle NotFound => 2
val smtgentim = (valOf o Real.fromString)
  (dfind "smtgentim" configd) handle NotFound => 5.0
val z3lem = string_to_int (dfind "z3lem" configd) handle NotFound => 32
val z3tim = string_to_int (dfind "z3tim" configd) handle NotFound => 2
val z3try = string_to_int (dfind "z3try" configd) handle NotFound => 10
val softmerge_flag = string_to_bool (dfind "softmerge_flag" configd) handle NotFound => false
val smtgentemp = (valOf o Real.fromString)
  (dfind "smtgentemp" configd) handle NotFound => 1.0

val nonesting = ref false

(* -------------------------------------------------------------------------
   Parsing functions
   ------------------------------------------------------------------------- *)

fun split_pair c s = pair_of_list (String.tokens (fn x => x = c) s)
  handle HOL_ERR _ => raise ERR "split_pair" (Char.toString c ^ ": " ^ s)

(* -------------------------------------------------------------------------
   Term functions
   ------------------------------------------------------------------------- *)

fun list_mk_comb_err (oper,argl) = list_mk_comb (oper,argl)
  handle HOL_ERR _ => (print_endline 
   (term_to_string oper ^ " : " ^ String.concatWith " | " 
    (map term_to_string argl)) 
; raise Parse)

fun list_mk_comb_err2 (oper,argl) = list_mk_comb (oper,argl)
  handle HOL_ERR _ => raise ERR "list_mk_comb_err2" 
(term_to_string oper ^ ": " ^ String.concatWith " " (map term_to_string argl))

fun mk_varn (n,k) = mk_var (n, rpt_fun_type (k+1) alpha) 
fun auto_comb (n,tml) = list_mk_comb_err (mk_varn (n,length tml),tml)
val var0 = mk_varn("0",0);

fun ite_template (t1,t2,t3) =
  auto_comb ("ite", [auto_comb ("<=", [t1,var0]),t2,t3]);
  
val xvar = ``x:'a``;
fun is_xvar x = term_eq x xvar;

fun contain_x tm = 
  let val (oper,argl) = strip_comb tm in
    is_xvar oper orelse exists contain_x argl
  end
 
(* language dependent *)
fun is_recvar v = is_var v andalso
  mem (hd_string (string_of_var v)) [#"w",#"v",#"s"]

fun contain_rec tm = 
  let val (oper,argl) = strip_comb tm in
    is_recvar oper orelse exists contain_rec argl
  end

fun is_nested tm =
  let val (oper,argl) = strip_comb tm in 
    is_recvar oper andalso exists contain_rec argl
  end;
  
fun contain_nested tm = (not o null o (find_terms is_nested)) tm;

fun acceptable tm = contain_x tm andalso contain_rec tm

fun term_compare_size (t1,t2) = cpl_compare Int.compare Term.compare
  ((term_size t1,t1), (term_size t2, t2));

(* -------------------------------------------------------------------------
   Evaluating predicates
   ------------------------------------------------------------------------- *)

local open IntInf in
  val aonem = fromInt (~1)
  val azero = fromInt 0
  val aone = fromInt 1
  val atwo = fromInt 2
  fun aincr x = x + aone
  fun adecr x = x - aone
  val maxint = fromInt (valOf (Int.maxInt))
  val minint = fromInt (valOf (Int.minInt))
  fun large_int x = x > maxint orelse x < minint
  fun arb_pow a b = if b <= azero then aone else a * arb_pow a (b-aone)
  fun pow2 b = arb_pow atwo (fromInt b)
  val maxarb = arb_pow (fromInt 10) (fromInt maxintsize)
  val minarb = ~maxarb
  val large_arb = 
    if !maxint_flag 
    then (fn x => x > maxarb orelse x < minarb)
    else (fn x => false)
end

val inputl = 
  let 
    val l1 = List.tabulate (10,IntInf.fromInt)
    val l1b = List.tabulate (15,fn x => IntInf.fromInt (x-5))
  in
    cartesian_product l1 l1b
  end

fun eval_term fed tm input =
  let 
    val _ = incr abstimer
    val _ = if !abstimer > !timelimit then raise ProgTimeout else ()
    val (oper,argl) = strip_comb tm
    fun binop f = 
      let 
        val (a,b) = pair_of_list argl 
        val r = f (eval_term fed a input, eval_term fed b input)
      in
        if large_arb r then raise ProgTimeout else r
      end   
  in
    case string_of_var oper of
      "0" => IntInf.fromInt 0
    | "1" => IntInf.fromInt 1
    | "2" => IntInf.fromInt 2
    | "+" => binop IntInf.+
    | "-" => binop IntInf.-
    | "*" => binop IntInf.*
    | "divf" => binop IntInf.div
    | "modf" => binop IntInf.mod
    | "ite" => let val (a,b,c) = triple_of_list argl in 
                 if eval_pred fed a input
                 then eval_term fed b input
                 else eval_term fed c input
               end
    | "x" => fst input
    | "y" => snd input
    | s => 
      case dfindo oper fed of
        NONE => raise ERR "eval_term" ("operator not found: " ^ s)
      | SOME f => 
        let val r = 
          (
          case argl of
            [] => f (IntInf.fromInt 0, IntInf.fromInt 0)
          | [a] => f (eval_term fed a input, IntInf.fromInt 0)
          | [a,b] =>  f (eval_term fed a input, eval_term fed b input)
          | _ => raise ERR "eval_term" "arity"
          )
        in
          if large_arb r then raise ProgTimeout else r
        end
  end

and eval_pred fed tm input =
  if is_conj tm then
    let val (a,b) = dest_conj tm in
      eval_pred fed a input andalso eval_pred fed b input
    end
  else if is_neg tm then not (eval_pred fed (dest_neg tm) input)
  else if is_imp tm then 
    let val (a,b) = dest_imp tm in
      not (eval_pred fed a input) orelse eval_pred fed b input
    end
  else if is_eq tm then
    let val (a,b) = dest_eq tm in
      eval_term fed a input = eval_term fed b input
    end
  else if string_of_var (fst (strip_comb tm)) = "<=" then
    let val (a,b) = pair_of_list (snd (strip_comb tm)) in
      eval_term fed a input <= eval_term fed b input
    end
  else raise ERR "eval_pred" "not a predicate"

fun add_cache f = 
  let 
    val d = ref (dempty (cpl_compare IntInf.compare IntInf.compare)) 
    fun newf input = 
      let val _ = 
        if dlength (!d) > 20000 
        then d := dempty (cpl_compare IntInf.compare IntInf.compare)
        else ()
      in
        case dfindo input (!d) of
        NONE => 
          let val (r,b) = (f input,true) 
            handle 
                Div => (IntInf.fromInt 0,false)
              | ProgTimeout => (IntInf.fromInt 1,false)
              | Overflow => (IntInf.fromInt 1,false)
              | Empty => (IntInf.fromInt 1,false)
          in
            d := dadd input (r,b) (!d); 
            if b then r else
            if r = IntInf.fromInt 0 then raise Div else raise ProgTimeout
          end      
       | SOME (r,b) => 
         if b then r else
         if r = IntInf.fromInt 0 then raise Div else raise ProgTimeout
     end
  in
    newf
  end

fun create_fed pp =
  let
    val fpl = get_recfpl_ws (progpair_to_progxpair_shared pp)
    val fed = dnew Term.compare 
      (map_snd (add_cache o exec_memo.mk_exec_twov) fpl)
  in
    fed
  end
  
fun true_pred fed pred =
  let
    fun f x = 
      (
      abstimer := 0;
        ( 
        eval_pred fed pred x handle
          Div => false
        | ProgTimeout => true
        | Overflow => true
        | Empty => true
        )
      )
  in
    all f inputl
  end

(* -------------------------------------------------------------------------
   Fingerprinting (add maxint_flag true to config for safety)
   ------------------------------------------------------------------------- *)

fun fenum f xltop =
  let
    fun init () = abstimer := 0
    fun loop acc xl = 
      (
      init ();
      if null xl 
      then SOME (rev acc)
      else loop (f (hd xl) :: acc) (tl xl)
      )
  in
    loop [] xltop handle
      Div => NONE
    | ProgTimeout => NONE
    | Overflow => NONE
  end;
  
fun fingerprint fed tm = case fenum (eval_term fed tm) inputl of NONE => NONE
  | SOME seq => SOME (seq,tm);


fun fenumb f xltop =
  let
    fun init () = abstimer := 0
    fun loop acc xl = 
      (
      init ();
      if null xl
      then SOME (rev acc)
      else loop (f (hd xl) :: acc) (tl xl)
      )
  in
    loop [] xltop handle
      Div => NONE
    | ProgTimeout => NONE
    | Overflow => NONE
  end;
  
fun fingerprintb fed tm = case fenumb (eval_pred fed tm) inputl of NONE => NONE
  | SOME seq => SOME (seq,tm);

(* -------------------------------------------------------------------------
   Generate and test terms
   ------------------------------------------------------------------------- *)

fun gen_true_eq fed tml =
  let
    val seqtml = List.mapPartial (fingerprint fed) tml;
    val d = dappendl seqtml (dempty (list_compare IntInf.compare));
    val l1 = dlist d;
    val l2 = filter (fn x => length (snd x) >= 2) l1;
    val l3 = map_snd (all_pairs o random_subset 3) l2;
    val l4 = map mk_eq (List.concat (map snd l3));
  in
    l4
  end;
  
val leqoper = mk_var ("<=",``:'a -> 'a -> bool``);
fun mk_leq (a,b) = list_mk_comb (leqoper, [a,b]); 
fun gen_eq tml = mk_eq (pair_of_list (random_subset 2 tml));
fun gen_leq tml = mk_leq (pair_of_list (random_subset 2 tml));

fun gen_true fed generator tml k = 
  let  
    val d = ref (eempty Term.compare)
    fun loop n = 
      (
      if n mod 100 = 0 then print "." else ();
      if elength (!d) >= k orelse n <= 0 then elist (!d) else
      let val r = generator tml in
        if true_pred fed r then d := eadd r (!d) else ();
        loop (n-1)
      end
      ) 
  in
    loop (100 * k)
  end;  

fun gen_partial fed generator tml k = 
  let  
    val d = ref (eempty Term.compare)
    fun loop n = 
      (
      if n mod 100 = 0 then print "." else ();
      if elength (!d) >= k orelse n <= 0 then elist (!d) else
      let val r = generator tml in
        if true_pred fed r orelse true_pred fed (mk_neg r) 
        then () 
        else d := eadd r (!d);
        loop (n-1)
      end
      ) 
  in
    loop (100 * k)
  end; 

fun is_truish bl = let val n = length (filter I bl) in
   n >= 75 andalso n < 150
   end;

fun gen_truish fed generator tml k = 
  let  
    val d = ref (eempty Term.compare)
    fun loop n = 
      (
      if n mod 100 = 0 then print "." else ();
      if elength (!d) >= k orelse n <= 0 then elist (!d) else
      let 
        val r = generator tml 
        val blo = fingerprintb fed r
      in
        if isSome blo andalso is_truish (fst (valOf blo)) 
        then d := eadd r (!d)
        else ();
        loop (n-1)
      end
      ) 
  in
    loop (10 * k)
  end; 

fun test_truish (seq1,seq2) = 
  is_truish (map (fn (x,y) => x = y) (combine (seq1,seq2)));

fun gen_truish_eq (seqtml : (IntInf.int list * term) list) k =
  let  
    val d = ref (eempty Term.compare)
    fun loop n = 
      (
      if n mod 100 = 0 then print "." else ();
      if elength (!d) >= k orelse n <= 0 then elist (!d) else
      let 
        val (seq1,t1) = random_elem seqtml
        val (seq2,t2) = random_elem seqtml
        val b = test_truish (seq1,seq2)
      in
        if b then d := eadd (mk_eq (t1,t2)) (!d) else ();
        loop (n-1)
      end
      ) 
  in
    loop (10 * k)
  end

(* conj *)
fun mk_varn (n,k) = mk_var (n, rpt_fun_type (k+1) alpha);
fun mk_svar tm = mk_varn ("s" ^ tl_string (string_of_var tm), arity_of tm);
fun mk_wvar tm = mk_varn ("w" ^ tl_string (string_of_var tm), arity_of tm);  
 
fun add_sw tm = 
  if hd_string (string_of_var tm) = #"w" 
  then [tm, mk_svar tm]
  else if hd_string (string_of_var tm) = #"s"
  then [tm, mk_wvar tm]
  else [tm] 

fun all_recvar tm = 
  let val (oper,argl) = strip_comb tm in 
    (if is_recvar oper then [oper] else []) @
    List.concat (map all_recvar argl)
  end 
 
fun all_recvar_sw tm = 
  mk_fast_set Term.compare (List.concat (map add_sw (all_recvar tm)));

(* disj *)
fun complement_score (seq1,tm1) (seq2,tm2) = 
  let val l = combine (seq1,seq2) in
    if not (all (fn (a,b) => a orelse b) l) 
    then NONE
    else SOME ((tm1,tm2),length (filter (fn (a,b) => a = b) l)) 
  end;

fun complement_ex alluslbl ex =
  let 
    val scl = List.mapPartial (complement_score ex) alluslbl
  in
    if null scl then NONE else 
    if random_real () < 0.5 
    then SOME (fst (random_elem scl))
    else SOME (fst (hd (dict_sort compare_imin scl)))
  end;
  
fun mk_imp_from_disj (a,b) = 
  let val a' = if is_neg a then dest_neg a else mk_neg a in
    mk_imp (a',b)
  end 

fun first_n_truepred fed n acc tml = 
  if n <= 0 then rev acc else
  case tml of
    [] => rev acc
  | tm :: m => if true_pred fed tm 
               then first_n_truepred fed (n-1) (tm :: acc) m
               else first_n_truepred fed n acc m 
  

fun gen_pp pp tml =
  let
    val fed = create_fed pp
    (* true *)
    val (eqtlfull,t) = add_time (gen_true_eq fed) tml
    val eqtl = random_subset 250 eqtlfull
    val _ = print_endline ("eqt in " ^ rts_round 2 t ^ " seconds")
    val (noteqtl,t) = add_time (gen_true fed (mk_neg o gen_eq) tml) 250
    val _ = print_endline ("noteqt in " ^ rts_round 2 t ^ " seconds")
    val (leqtl,t) = add_time (gen_true fed  gen_leq tml) 250;
    val _ = print_endline ("leqt in " ^ rts_round 2 t ^ " seconds")
    val (notleqtl,t) = add_time (gen_true fed (mk_neg o gen_leq) tml) 250
    val _ = print_endline ("notleqt in " ^ rts_round 2 t ^ " seconds")
    val alltl = eqtl @ noteqtl @ leqtl @ noteqtl
    val _ = print_endline "true"
    (* conj *)
    val alltlsw = map_assoc all_recvar_sw alltl
    fun is_conjable ((t1,l1),(t2,l2)) = 
      if exists (fn x => tmem x l2) l1
      then SOME (mk_conj (t1,t2)) 
      else NONE;
    val (conjlfull,t) = add_time 
      (List.mapPartial is_conjable) (all_pairs alltlsw)
    val conjl = random_subset 1000 conjlfull
    val _ = print_endline (its (length conjl) ^ " conjunctions in " ^
      rts_round 2 t ^ " seconds")
    (* undecided *)
    val (equl,t) = add_time (gen_partial fed gen_eq tml) 250;
    val _ = print_endline ("equ in " ^ rts_round 2 t ^ " seconds")
    val (notequl,t) = add_time (gen_partial fed (mk_neg o gen_eq) tml) 250;
    val _ = print_endline ("notequ in " ^ rts_round 2 t ^ " seconds")
    val (lequl,t) = add_time (gen_partial fed gen_leq tml) 250;
    val _ = print_endline ("lequ in " ^ rts_round 2 t ^ " seconds")
    val (notlequl,t) = add_time (gen_partial fed (mk_neg o gen_leq) tml) 250;
    val _ = print_endline ("notlequ in " ^ rts_round 2 t ^ " seconds")
    val allul = equl @ notequl @ lequl @ notequl;
    val _ = print_endline "undecided"
    (* equiv *)
    fun mk_equiv (a,b) = mk_conj (mk_imp (a,b),mk_imp (b,a));
    val equivl = map mk_equiv (all_pairs allul);
    val (equivtl,t) = add_time (first_n_truepred fed 1000 []) (shuffle equivl);
    val _ = print_endline (its (length equivtl) ^ " equivalences in " ^
      rts_round 2 t ^ " seconds")
    (* truish *)
    val seqtml = List.mapPartial (fingerprint fed) tml;
    val (eqsl,t) = add_time (gen_truish_eq seqtml) 250
    val _ = print_endline ("eqs in " ^ rts_round 2 t ^ " seconds")
    val (noteqsl,t) = add_time (gen_truish fed (mk_neg o gen_eq) tml) 250;
    val _ = print_endline ("noteqs in " ^ rts_round 2 t ^ " seconds")
    val (leqsl,t) = add_time (gen_truish fed gen_leq tml) 250;
    val _ = print_endline ("leqs in " ^ rts_round 2 t ^ " seconds")
    val (notleqsl,t) = add_time (gen_truish fed (mk_neg o gen_leq) tml) 250
    val _ = print_endline ("notleqs in " ^ rts_round 2 t ^ " seconds")
    val allsl = eqsl @ leqsl @ notleqsl @ noteqsl;
    val _ = print_endline "truish"
    (* combine truish and undecided *)
    val allusl = equl @ eqsl @ lequl @ notlequl @ leqsl @ 
                 notleqsl @ notequl @ noteqsl
    (* disj *)
    val allslbl = List.mapPartial (fingerprintb fed) allsl
    val alluslbl = List.mapPartial (fingerprintb fed) allusl
    val (disjlsep,t) = 
      add_time (List.mapPartial (complement_ex alluslbl)) allslbl
    val _ = print_endline (its (length disjlsep) ^ " implications in " ^
      rts_round 2 t ^ " seconds")
    val disjl = map mk_imp_from_disj disjlsep
  in
    filter acceptable 
    (mk_fast_set Term.compare (alltl @ conjl @ equivtl @ disjl))
  end  
 

(*
load "kolmo";
open aiLib kernel smt_hol progx smt_progx kolmo;
val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sem");
val (a,pp) = random_elem appl;
val tml = kolmo_pp pp 6;
load "search_term"; open search_term;
val inductl = gen_pp pp tml;

*)


(* -------------------------------------------------------------------------
   Operator to produce SMT formulas
   A B C D E F G H I            J    K L M     N     O P  Q   R       S   T
   0 1 2 + - * / % if then else loop x y compr loop2 = <= and implies not z
   ------------------------------------------------------------------------- *)

fun fake_var s = mk_var (s,``:num -> num``)

val smt_operl_term = map (fn (x,i) => mk_var (x, rpt_fun_type (i+1) alpha))
  [("0",0),("1",0),("2",0),
   ("+",2),("-",2),("*",2),("divf",2),("modf",2),
   ("ite",3)] @ 
   [fake_var "loop"] @
   map (fn x => mk_var (x, alpha)) ["x","y"] @
   map fake_var ["compr","loop2"]
  
val smt_operl_pred = 
 [mk_thy_const {Name="=", Thy="min", Ty=``:'a -> 'a -> bool``},
  mk_var ("<=",``:'a -> 'a -> bool``)];

val smt_operl_logic = [``$/\``,``$==>``,``$~``];

val extra_var = [mk_var ("z",alpha)]

val smt_operl = smt_operl_term @ smt_operl_pred @ smt_operl_logic @ extra_var

val smt_operd = enew Term.compare smt_operl

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

val prog_counter = ref 0
val afd_glob = ref (dempty Term.compare)
val progd = ref (dempty (list_compare IntInf.compare))

(* -------------------------------------------------------------------------
   Available moves
   ------------------------------------------------------------------------- *)

fun is_boolty x = x = bool
fun is_alphaty x = x = alpha

fun is_termoper f = 
  let val (tyl,ty) = strip_type (type_of f) in
    is_alphaty ty
  end

fun is_predoper f =
  let val (tyl,ty) = strip_type (type_of f) in
    is_boolty ty andalso all is_alphaty tyl
  end

fun is_logicoper f = 
  let val (tyl,ty) = strip_type (type_of f) in
    is_boolty ty andalso all is_boolty tyl
  end

fun available_move (board1,board2) move = 
  if is_termoper move
    then 
      if !nonesting andalso is_recvar move andalso 
         length_geq board1 (arity_of move) andalso
         exists contain_rec (first_n (arity_of move) board1)
      then false 
      else length_geq board1 (arity_of move)
  else if is_predoper move
    then length_geq board1 (arity_of move) andalso
         not (term_eq (List.nth (board1,0)) (List.nth (board1,1)))
  else if is_logicoper move
    then
      (* if not (null board1) then false else *) 
      if term_eq move ``$~`` andalso not (null board2) andalso 
         is_neg (hd board2)
      then false
      else length_geq board2 (arity_of move)
  else raise ERR "availaible_move" (term_to_string move)

fun available_movel fl board = filter (available_move board) fl

(* -------------------------------------------------------------------------
   Apply a move
   ------------------------------------------------------------------------- *)

(*
if not (null (!subtml_glob)) andalso random_real () < 0.01 
    then (random_elem (!subtml_glob) :: board1, board2)
*)

fun apply_move move (board1,board2) =
  if is_termoper move then 
    let 
      val arity = arity_of move
      val (l1,l2) = part_n arity board1
    in
      if is_var move andalso string_of_var move = "ite" 
      then (ite_template (triple_of_list l1) :: l2, board2)
      else (list_mk_comb_err2 (move, l1) :: l2, board2)
    end
  else if is_predoper move then
    let 
      val arity = arity_of move
      val (l1,l2) = part_n arity board1
    in
      (l2, list_mk_comb_err2 (move, l1) :: board2)
    end
  else if is_logicoper move then
    let 
      val arity = arity_of move
      val (l1,l2) = part_n arity board2
    in
      (board1, list_mk_comb_err2 (move, l1) :: l2)
    end
  else raise ERR "apply_move" (term_to_string move)
  
(* -------------------------------------------------------------------------
   Save a program if it generates something new
   ------------------------------------------------------------------------- *)

fun save_program board = case board of
    (t :: _, _) => 
    let val l = [] in
      case dfindo l (!progd) of
        NONE => progd := dadd l t (!progd)
      | SOME told => if term_compare_size (t,told) = LESS 
                     then progd := dadd l t (!progd)
                     else ()
    end
  | _ => ()

(* -------------------------------------------------------------------------
   Distributing visits in advance according to policy part of MCTS formula
   ------------------------------------------------------------------------- *)

fun best_move distop = 
  if null distop then raise ERR "best_move" "" else
  let 
    fun loop (maxmove,maxsc) dis = case dis of
        [] => maxmove
      | ((a,b),c) :: m =>
        let val sc = b / (Real.fromInt (c + 1)) in
          if sc > maxsc then loop (a,sc) m else loop (maxmove,maxsc) m
        end
    val ((atop,btop),ctop) = hd distop
    val sctop = btop / (Real.fromInt (ctop + 1))
  in
    loop (atop,sctop) distop
  end     
     
fun inc_bestmove dis = 
  let val i = best_move dis in
    map (fn ((a,b),c) => if term_eq a i then ((a,b),c+1) else ((a,b),c)) dis
  end
 
fun split_vis nvis dis = 
  let 
    fun rm_polv ((a,b),c) = (a,c)
    fun f (_,b) =
      let val c = Real.floor (b * Real.fromInt nvis) in
        if c < 0 then 0 else if c >= nvis then nvis - 1 else c
      end
    val dis1 = map_assoc f dis 
    val missing = nvis - sum_int (map snd dis1)
    val dis2 = funpow missing inc_bestmove dis1
  in
    map rm_polv dis1
  end

(* -------------------------------------------------------------------------
   Allocate time in advance according to the prior probabilities
   ------------------------------------------------------------------------- *)
   
fun split_tim (torg,tinc) dis = 
  let 
    fun rm_polv ((a,b),c) = (a,c)
    val sum = ref 0.0
    fun f (_,b) =
      let 
        val c = b * tinc
        val newinc = if c < 0.0 then 0.0 else if c >= tinc then tinc else c
        val neworg = torg + !sum
        val _ = sum := !sum + newinc
      in  
        (neworg,newinc)
      end
  in
    map rm_polv (map_assoc f dis)
  end

(* -------------------------------------------------------------------------
   Allocate time in advance according to the prior probabilities
   ------------------------------------------------------------------------- *) 

fun create_pol ml =
  let fun f move = 
    if Real.compare (smtgentemp,1.0) = EQUAL then random_real () else
    let val r = random_real () in 
      Math.pow (Math.e, (1.0 / smtgentemp) * r) 
    end
  in
    normalize_distrib (map_assoc f ml)
  end

(* -------------------------------------------------------------------------
   Search limited by number of visits or a timeout
   ------------------------------------------------------------------------- *)

datatype searchlimit = Visits of int | Seconds of real * real

fun search_move_vis rt depth fl board (move,vis) =
  if vis <= 0 then () else
  search_aux rt depth (Visits vis) fl (apply_move move board)

and search_move_tim rt depth fl board (move,(torg,tinc)) =
  if torg + tinc <= Time.toReal (Timer.checkRealTimer rt) then () else
  search_aux rt depth (Seconds (torg,tinc)) fl (apply_move move board)

and search_move rt depth lim fl board pol = case lim of
    Seconds tim =>
    app (search_move_tim rt depth fl board) (split_tim tim pol)
  | Visits vis =>
    if vis - 1 <= 0 then () else
    app (search_move_vis rt depth fl board) (split_vis (vis - 1) pol)

and search_aux rt depth lim fl board = 
  if depth >= maxproglen_treesearch then () else
  let
    val _ = save_program board   
    val pol = create_pol (available_movel fl board)
  in
    search_move rt (depth + 1) lim fl board pol
  end


fun search fl lim =
  let
    val _ = if !ngen_glob <= 0 then timeincr := init_timeincr else ()
    val _ = progd := dempty (list_compare IntInf.compare)
    val _ = afd_glob := dempty Term.compare
    val rt = Timer.startRealTimer ()
    val depth = 0    
    val board = ([],[])
    fun test move = 
      not (tmem move (smt_operl_pred @ smt_operl_logic)) andalso
      not (is_var move andalso
      mem (string_of_var move) 
        ["*","divf","modf","ite","loop","loop2","compr"])  
    val newfl = filter test fl
    val (_,t) = add_time (search_aux rt depth lim newfl) board
    val tml = map snd (dlist (!progd))
  in
    print_endline (its (dlength (!progd)) ^ " predicates " ^ 
      "in "  ^ rts_round 2 t ^ " seconds");
    tml
  end

fun forallxy tm = 
  let 
    val vl = [``x:'a``,``y:'a``]
    val vl' = filter (fn x => tmem x vl) (free_vars tm) 
  in
    list_mk_forall (vl',tm)
  end

fun search_smt fl t = search (smt_operl @ fl) (Seconds (0.0,t))



(* -------------------------------------------------------------------------
   Induction axiom
   ------------------------------------------------------------------------- *)

fun mk_varn (n,k) = mk_var (n, rpt_fun_type (k+1) alpha) 
fun auto_comb (n,tml) = list_mk_comb_err (mk_varn (n,length tml), tml)
val xvar = mk_var ("x",alpha)
val yvar = mk_var ("y",alpha)
val zvar = mk_var ("z",alpha)
val var0 = mk_varn("0",0);
val var1 = mk_varn("1",0);
val xvari = auto_comb ("+",[xvar,var1]);
val pvar = mk_var ("P", ``:'a -> 'a -> 'a -> bool``)

(* 
fun simp_forall_once tm = 
  let 
    val (vl,body) = strip_forall tm 
    val vlin = free_vars body
    val vl' = filter (fn x => tmem x vlin) vl 
  in
    list_mk_forall (vl',body)
  end
*)
(* remove z if it does not appear *)
fun simp_forall_once tm = 
   let val (vl,body) = strip_forall tm in
     if contain_z body then tm else 
     list_mk_forall (filter (fn x => not (is_zvar x) vl),body)
   end
   
fun simp_forall tm = 
  if is_forall tm then simp_forall_once tm
  else if is_conj tm then
    let val (a,b) = dest_conj tm in mk_conj (simp_forall a, simp_forall b) end
  else if is_neg tm then mk_neg (simp_forall (dest_neg tm))
  else if is_imp tm then 
    let val (a,b) = dest_imp tm in mk_imp (simp_forall a, simp_forall b) end
  else raise ERR "simp_forall" ""


val induct_axiom =
  let 
    fun fP x y z = list_mk_comb_err (pvar,[x,y,z])
    val base_tm = list_mk_forall ([yvar,zvar], fP var0 yvar zvar)
    val imp_tm = list_mk_forall ([xvar,yvar,zvar],
      mk_imp (fP xvar yvar zvar, fP xvari yvar zvar))
    val leq = mk_var ("<=",``:'a -> 'a -> bool``)
    val cond = list_mk_comb_err (leq,[var0,xvar])
    val concl_tm = list_mk_forall ([xvar,yvar,zvar],
      mk_imp (cond, fP xvar yvar zvar))  
  in
    mk_imp (mk_conj (base_tm,imp_tm), concl_tm)
  end

fun beta_reduce x = (rhs o concl o REDEPTH_CONV BETA_CONV) x 
  handle UNCHANGED => x;

fun induct_cj cj =
  let 
    val xcj = list_mk_abs ([xvar,yvar,zvar],cj)
    val sub = [{redex = pvar, residue = xcj}]
  in
    simp_forall (beta_reduce (subst sub induct_axiom))
  end

fun get_subtml pp =
  let
    val (px1,px2) = progpair_to_progxpair_shared pp;
    val pxxl = mk_fast_set progx_compare_size 
        (all_subprog px1 @ all_subprog px2);
    val subtml = map pxx_to_hol_aux pxxl
  in
    subtml
  end


(* -------------------------------------------------------------------------
   Fuzzify macros so that every lowercase letter is used
   ------------------------------------------------------------------------- *)

val macron_glob = 20

fun fuzzify_macro_aux mn id = 
  let 
    val idl = 
      let 
        val l = ref [id] 
        fun loop start = 
          if start + mn >= macron_glob then () else 
          (l := start+mn :: (!l); loop (start+mn))
    
        in
          loop id; !l
        end
  in
    random_elem idl
  end
 
fun fuzzify_macro mn id = 
  if random_real () > 0.1 then id else fuzzify_macro_aux mn id;   
 
fun unfuzzify_macro mn id = id mod mn

(* -------------------------------------------------------------------------
   Conversion from term to tree (special case for if then else)
   ------------------------------------------------------------------------- *)

datatype nmt = Upper of int | Lower of int | Subf of int * int

fun nmt_compare (atop,btop) = case (atop,btop) of
    (Upper a, Upper b) => Int.compare (a,b)
  | (Upper _, _ ) => LESS
  | (_ , Upper _) => GREATER
  | (Lower a, Lower b) => Int.compare (a,b)
  | (Lower _, _) => LESS
  | (_, Lower _) => GREATER
  | (Subf a, Subf b) => cpl_compare Int.compare Int.compare (a,b)

fun uppercase id = Char.toString (Char.chr (65 + id));
fun lowercase id = Char.toString (Char.chr (97 + id));
fun digit id = Char.toString (Char.chr (48 + id));

fun nmt_to_string x = case x of
    Upper a => uppercase a 
  | Lower a => lowercase a
  | Subf (a,b) => lowercase a ^ digit b
   
datatype nmttree = Insn of (nmt * nmttree list)

fun induct_to_prog d tm = 
  let 
    val (oper,argl) = strip_comb tm 
    val opern = dfind oper d 
      handle NotFound => raise ERR "induct_to_prog" (term_to_string oper)
  in
    if opern = Upper 8 (* ite *)
    then
      let 
        val (a,b,c) = triple_of_list argl 
        val a1 = fst (pair_of_list (snd (strip_comb a)))
      in
        Insn (opern, map (induct_to_prog d) [a1,b,c])
      end
    else Insn (opern, map (induct_to_prog d) argl)
  end

fun prog_to_induct d (Insn (opern,pl)) =
  if opern = Upper 8 then 
    let val (a,b,c) = triple_of_list (map (prog_to_induct d) pl) in
      ite_template (a,b,c)
    end
  else
    let val oper = dfind opern d
      handle NotFound => raise ERR "prog_to_induct" (nmt_to_string opern)
    in 
      list_mk_comb_err (oper, map (prog_to_induct d) pl)
    end

(* -------------------------------------------------------------------------
   Conversion from tree to leaf list
   ------------------------------------------------------------------------- *)

fun prog_to_idl (Insn (i,pl)) = i :: List.concat (map prog_to_idl pl)

fun idl_to_progl d idl = case idl of
    [] => []
  | id :: m => 
    let
      val pl = idl_to_progl d m
      val oper = dfind id d
        handle NotFound => raise ERR "idl_to_prog" (nmt_to_string id)
      val arity = arity_of oper
      val (pl1,pl2) = part_n arity pl
    in
      if length pl1 <> arity 
      then 
      (print_endline (term_to_string oper ^ " " ^  
                      nmt_to_string id ^ " " ^ its arity
                      ^ " " ^ its (length pl));                
       raise Parse) 
      else Insn (id,pl1) :: pl2
    end
    

(* -------------------------------------------------------------------------
   Conversion from leaf list to string list
   ------------------------------------------------------------------------- *)

fun lowercasef mn id = Char.toString (Char.chr (97 + fuzzify_macro mn id));

fun is_digit n = n < 65
fun is_upper n = n >= 65 andalso n < 97
fun is_lower n = n >= 97

fun mk_lower mn n = Lower (unfuzzify_macro mn (n - 97))
fun mk_upper n = Upper (n - 65)
fun mk_sub mn (n1,n2) = Subf (unfuzzify_macro mn (n1 - 97), n2 - 48)

fun id_to_string mn id = case id of
    Upper k => uppercase k
  | Lower k => lowercasef mn k
  | Subf (k1,k2) => lowercasef mn k1 ^ " " ^ digit k2

fun idl_to_string mn idl = String.concatWith " " (map (id_to_string mn) idl)

fun bad_id n = mem (n - 65) [9,12,13]

fun string_to_idl mn s = 
  let 
    val nl = map (fn x => Char.ord (valOf (Char.fromString x)))
      (String.tokens Char.isSpace s)
    val _ = if exists bad_id nl then raise Parse else ()
    fun regroup_id l = case l of 
        [] => []
      | [n] => 
        if is_digit n then raise ERR "string_to_idl" "digit"
        else if is_upper n then [mk_upper n]
        else if is_lower n then [mk_lower mn n]
        else raise ERR "string_to_idl" "unexpected"
      | n1 :: n2 :: m => 
        if is_digit n1 then raise ERR "string_to_idl" "digit"
        else if is_upper n1 then mk_upper n1 :: regroup_id (n2 :: m) 
        else if is_lower n1 then 
          if is_digit n2 then mk_sub mn (n1,n2) :: regroup_id m
          else mk_lower mn n1 :: regroup_id (n2 :: m) 
        else raise ERR "string_to_idl" "unexpected"
  in
    regroup_id nl
  end

(* -------------------------------------------------------------------------
   Create conversion dictionaries
   ------------------------------------------------------------------------- *)

fun get_index tm = string_to_int (tl_string (string_of_var tm))

fun compare_indices (tm1,tm2) = Int.compare (get_index tm1,get_index tm2);

fun compare_fnames (tm1,tm2) = Int.compare 
  (Char.ord (hd_string (string_of_var tm1)), 
   Char.ord (hd_string (string_of_var tm2)))
   
fun is_s tm = hd_string (string_of_var tm) = #"s"   
   
fun extract_s (x,tml) = 
  let val (l1,l2) = partition is_s tml in
    if null l1 then [(x,tml)] else [(x,l2),(singleton_of_list l1,[])]
  end
  
fun get_recfl_sub tml = 
  let
    val l1 = map (fn x => (get_index x,x)) tml
    val l2 = map snd (dlist (dregroup Int.compare l1))
    val l3 = map (dict_sort compare_fnames) l2
    val l4 = map (fn l => (last l,butlast l)) l3
    val l5 = List.concat (map extract_s l4)
  in
    l5
  end;   

fun assoc_ftm_id pp = 
  let
    fun h (tm,i) = (tm, Upper i)
    val upperl = map h (number_snd 0 smt_operl)
    fun decl_to_oper tm = 
      let 
        val (a,b) = dest_eq (snd (strip_forall tm))
        val (oper,argl) = strip_comb a
      in
        oper
      end
    val tml10 = create_decl_only pp
    val _ = if !debug_flag
            then app (print_endline o term_to_string) tml10
            else ()
    val tml0 = mk_fast_set Term.compare (map decl_to_oper tml10)
    val tml1 = get_recfl_sub tml0
    val tml2 = number_snd 0 tml1
    val mn = length tml2
    fun g i (tm,j) = (tm, Subf (i,j))
    fun f ((tm,tml),i) = (tm, Lower i) :: map (g i) (number_snd 0 tml)
    val tml3 = List.concat (map f tml2)
  in
    (mn, upperl @ tml3)
  end

(* -------------------------------------------------------------------------
   Conversion (all-in-one)
   ------------------------------------------------------------------------- *)
   
fun induct_to_string mn d tm = 
  (idl_to_string mn o prog_to_idl o induct_to_prog d) tm

fun string_to_induct mn d s = 
  let 
    fun hd_err x = hd x handle Empty => raise Parse 
    val idl = string_to_idl mn s
    val _ = 
      if !debug_flag 
      then print_endline (String.concatWith " " (map nmt_to_string idl))
      else ()
    val prog = hd_err (idl_to_progl d idl) 
    val tm = prog_to_induct d prog
  in 
    tm 
  end
  
  
fun inductl_to_stringl pp tml = 
  let 
    val (mn,l) = assoc_ftm_id pp
    val d = dnew Term.compare l 
  in
    map (induct_to_string mn d) tml
  end

fun stringl_to_inductl pp sl =
  let 
    val (mn,l) = assoc_ftm_id pp
    val _ = if not (!debug_flag) then () else 
      let 
        val _ = print_endline "dictionary"
        fun f (tm,id) = term_to_string tm ^ " @ " ^ nmt_to_string id 
      in
        print_endline (String.concatWith " | " (map f l))
      end
    val d = dnew nmt_compare (map swap l) 
  in
    map (string_to_induct mn d) sl
  end
  
fun stringl_to_inductl_option pp sl =
  let
    val (mn,l) = assoc_ftm_id pp
    val d = dnew nmt_compare (map swap l)
    fun f s = 
      let val r = string_to_induct mn d s in 
        if type_of r = bool then SOME r else NONE 
      end 
      handle Parse => NONE
  in
    List.mapPartial f sl
  end  

(* -------------------------------------------------------------------------
   Running Z3 with induction predicates
   ------------------------------------------------------------------------- *)

fun read_status file =
  if not (exists_file file) orelse null (readl file) 
  then "unknown"
  else String.concatWith " " (String.tokens Char.isSpace (hd (readl file)));
  
val z3_bin = selfdir ^ "/z3"

fun z3_cmd t1s t2s filein fileout = String.concatWith " "
  ["timeout",t1s,z3_bin,t2s,filein,">",fileout]

fun z3_prove filein fileout t decl inductltop =
  let 
    val inductl = map induct_cj inductltop
    val cmd = z3_cmd (its (t div 1000 + 1)) ("-t:" ^ its t) filein fileout
    val _ = write_induct_pb filein decl inductl
    val _ = OS.Process.system cmd
    val _ = OS.Process.sleep (Time.fromReal 0.1)
    val s = read_status fileout
    val _ = app remove_file [filein,fileout]
  in 
    s = "unsat"
  end

(* -------------------------------------------------------------------------
   Printing pairs of programs with tags and without tags
   ------------------------------------------------------------------------- *)

fun id_to_nmt id = Char.toString (Char.chr (65 + id));
fun nmt_to_id s = Char.ord (valOf (Char.fromString s)) - 65
fun nmt_macro i = Char.toString (Char.chr (97 + i));

(* write tagged programs *)
fun vo_to_idl recd vo = case vo of 
    NONE => []
  | SOME s => if hd_string s = #"w" 
              then [dfind s recd, dfind ("s" ^ tl_string s) recd]
              else [dfind s recd];
               
fun px_to_sl recd (Insx ((i,vo),pl)) = 
  id_to_nmt i :: (vo_to_idl recd vo) @ List.concat (map (px_to_sl recd) pl);

fun px_to_string recd px = String.concatWith " " (px_to_sl recd px);

fun pp_to_stringtag pp = 
  let 
    fun create_recd ppx =
      let 
        val l1 = map string_of_var (get_recfl_ws ppx); 
        val l2 = List.tabulate (length l1, nmt_macro)
      in
        dnew String.compare (combine (l1,l2))
      end
    val ppx = progpair_to_progxpair_shared pp
    val recd = create_recd ppx
  in
    px_to_string recd (fst ppx) ^ "=" ^ px_to_string recd (snd ppx)
  end

(* read tagged programs *)
fun idl_to_pxl idl = case idl of
    [] => []
  | id :: m => 
    let
      val pl = idl_to_pxl m
      val arity = arity_of_oper id
      val (pl1,pl2) = part_n arity pl
    in
      if length pl1 <> arity then raise Parse else Ins (id,pl1) :: pl2
    end

fun stringtag_to_prog s = 
  let 
    val sl1 = String.tokens Char.isSpace s
    val sl2 = filter (fn x => Char.isUpper (valOf (Char.fromString x))) sl1
    val idl = map nmt_to_id sl2
    val pl = idl_to_pxl idl
  in
    singleton_of_list pl handle HOL_ERR _ => raise ERR "stringtag_to_prog" s
  end
  
fun stringtag_to_pp s =
  let val (s1,s2) = split_pair #"=" s in
    (stringtag_to_prog s1, stringtag_to_prog s2)
  end

(* -------------------------------------------------------------------------
   Generating random induction predicates
   ------------------------------------------------------------------------- *)

fun filter_eval (pp,il1) =
  let
    val _ = print_endline "evaluation initialization"
    val fed = create_fed pp 
    val _ = print_endline "evaluation"
    fun test i = true_pred fed i handle Interrupt => raise Interrupt | _ => 
      (print_endline ("error during evaluation of " ^ term_to_string i); true)
    val (il2,t) = add_time (filter test) il1
    val _ = print_endline (its (length il2) ^ 
      " true predicates in " ^ rts_round 2 t ^ " seconds")
  in
    il2
  end
  handle Interrupt => raise Interrupt | _ => 
    (print_endline ("error during evaluation initialization"); il1)

fun random_inductl pp = 
  let
    val recfl = get_recfl_ws (progpair_to_progxpair_shared pp)
    val _ = print_endline (its (length recfl) ^ " recursive functions")
    (* val _ = subtml_glob := get_subtml pp
       val _ = print_endline (its (length (!subtml_glob)) ^ " subterms") *)
    (* 
    val _ = nonesting := false
    val il1 = search_smt recfl smtgentim
    *)
    val _ = nonesting := true
    val il2 = search_smt recfl smtgentim
    val il3 = mk_fast_set Term.compare il2
  in
    il3 (* filter_eval (pp,il3) *)
  end

fun ppil_to_string (pp,il) = 
  pp_to_stringtag pp ^ ">" ^ 
  (if null il then "empty" else
   (String.concatWith "|" (inductl_to_stringl pp il)))

fun write_inductl file l = writel file (map ppil_to_string l)

fun random_inductl_string pps =
  let 
    val pp = stringtag_to_pp pps 
    val il = random_inductl pp 
  in
    ppil_to_string (pp,il)
  end

(* -------------------------------------------------------------------------
   Proof: parsing
   ------------------------------------------------------------------------- *)

val ignore_errors = ref true

fun parse_ppil ppils =
  let 
    val (s1,s2) = split_pair #">" ppils
    val pp = stringtag_to_pp s1 
    val sl = if s2 = "empty" then [] else String.tokens (fn x => x = #"|") s2
    val _ = print_endline (its (length sl) ^ " induction predicates")
    val il = if !ignore_errors 
             then stringl_to_inductl_option pp sl
             else stringl_to_inductl pp sl
    val _ = print_endline (its (length sl - length il) ^ " parse errors")
  in
    (pp,il)
  end

fun parse_ippil ippils =
  let val (jobns,ppils) = split_pair #":" ippils in
    (jobns, parse_ppil ppils)
  end


val inductl_cmp = list_compare
  (cpl_compare (cpl_compare prog_compare prog_compare) 
  (list_compare Term.compare))
  
fun read_inductl file = map parse_ppil (readl file)

fun write_ppils_pb file ppils = 
  let
    val (pp,il) = parse_ppil ppils
    val decl = create_decl pp
    val inductl = map induct_cj il
  in
    write_induct_pb file decl inductl
  end
  
fun write_ppils_pbl expname =   
  let 
    val dir = selfdir ^ "/exp/" ^ expname
    val pbdir = dir ^ "/pb"
    val sl = readl (dir ^ "/current")
    val _ = mkDir_err pbdir
    fun f i s = write_ppils_pb (pbdir ^ "/" ^ its i) s
  in
    appi f sl
  end

(* -------------------------------------------------------------------------
   Re-proving
   ------------------------------------------------------------------------- *)

fun z3_reprove_inductl filein fileout pp inductl = 
  let
    val _ = print_endline "declare functions"
    val decl = create_decl pp
    val _ = print_endline (its (length decl) ^ " declarations")
    val _ = print_endline (its (length inductl) ^ " induction instances")
    val _ = print_endline ("z3 timeout: " ^ its z3tim ^ " milliseconds")
    val (b,t) = add_time (z3_prove filein fileout z3tim decl) inductl
    val _ = 
      if b 
      then print_endline ("unsat in " ^ rts_round 2 t ^ " seconds")
      else print_endline ("unknown in " ^ rts_round 2 t ^ " seconds")
  in
    if b then "unsat" else "unknown"
  end

fun z3_reprove_ppil_aux (i,(pp,il)) =
  let
    val filein = selfdir ^ "/z3_" ^ i ^ "_in.smt2"
    val fileout = selfdir ^ "/z3_" ^ i ^ "_out"
    val r = z3_reprove_inductl filein fileout pp il
  in
    r
  end

fun z3_reprove_ppil s = 
  let 
    val (i,(pp,il1)) = parse_ippil s
    val _ = print_endline (pp_to_stringtag pp)
    val _ = print_endline (human.humanf (fst pp) ^ " = " ^ 
                           human.humanf (snd pp))
    val _ = print_endline (its (length il1) ^ " predicates")
  in
    z3_reprove_ppil_aux (i,(pp,il1))
  end

fun tag_job l = map (fn (i,x) => its i ^ ":" ^ x) (number_fst 0 l)  

fun z3_reprove_para expname = 
  if expname = "" then raise ERR "z3_reprove_para" "empty expname" else
  let
    val expdir = selfdir ^ "/exp"
    val dir = expdir ^ "/" ^ expname
    fun log s = append_endline (dir ^ "/log") s
    fun logl l s = log (its (length l) ^ " " ^ s)
    val _ = app mkDir_err [expdir,dir]
    val l1 = readl (dir ^ "/current")
    val _ = logl l1 "targets"
    val (l2,t) = add_time 
      (parmap_sl ncore "search_term.z3_reprove_ppil") (tag_job l1)
    val _ = log ("reprove time: " ^ rts_round 2 t)
    val n = length (filter (fn x => x = "unsat") l2)
    val _ = log ("success rate: " ^ its n ^ " out of " ^ its (length l1))
  in 
    ()
  end

(* -------------------------------------------------------------------------
   Proof: calling z3
   ------------------------------------------------------------------------- *)

fun z3_prove_inductl filein fileout pp inductl = 
  let
    val _ = print_endline "declare functions"
    val decl = create_decl pp
    val _ = print_endline (its (length decl) ^ " declarations")
    val _ = print_endline (its (length inductl) ^ " induction instances")
    val _ = print_endline (its z3try ^ " tries")
    val _ = print_endline ("z3 timeout: " ^ its z3tim ^ " milliseconds")
    val _ = print_endline (its z3lem ^ " sampled lemmas")
    fun provable t sel = 
      z3_prove filein fileout t decl sel
    fun minimize acc sel = case sel of 
        [] => (print_endline (its (length acc) ^ " minimized lemmas");
               String.concatWith "|" ("unsat" :: inductl_to_stringl pp acc))
      | a :: m =>
        if not (provable z3tim (acc @ m))
        then minimize (acc @ [a]) m
        else minimize acc m
    fun minimize_wrap sel = 
      let val (r,t) = add_time (minimize []) sel in
        print_endline ("minimization time: " ^ rts_round 2 t ^ " seconds"); r
      end
    fun loop n = 
      if n <= 0 then (print_endline "unknown"; "unknown") else 
      let 
        val sel = random_subset z3lem inductl
        val (b,t1) = add_time (z3_prove filein fileout z3tim decl) sel
      in 
        if b then (print_endline 
          ("proof found after " ^ its (z3try - n + 1) ^ " tries in " ^
           rts_round 2 t1 ^ " seconds")
          ; minimize_wrap sel) else loop (n-1)
      end
    val (r,t) = add_time loop z3try
    val _ =  print_endline ("total proving time (includes minimization): " ^ 
      rts_round 2 t)
  in
    r
  end

fun good_pp pp = 
  let val recfl = get_recfl_ws (progpair_to_progxpair_shared pp) in
    length recfl <= 20
  end

fun z3_prove_ppil_aux (i,(pp,il)) =
  let
    val filein = selfdir ^ "/z3_" ^ i ^ "_in.smt2"
    val fileout = selfdir ^ "/z3_" ^ i ^ "_out"
    val r = z3_prove_inductl filein fileout pp il
  in
    pp_to_stringtag pp ^ ">" ^ r
  end

fun z3_prove_ppil s = 
  let 
    val (i,(pp,il1)) = parse_ippil s
    val _ = print_endline (pp_to_stringtag pp)
    val _ = print_endline (human.humanf (fst pp) ^ " = " ^ 
                           human.humanf (snd pp))
    val _ = print_endline (its (length il1) ^ " predicates")
    val il2 = filter_eval (pp,il1)
  in
    z3_prove_ppil_aux (i,(pp,il2))
  end


(* -------------------------------------------------------------------------
   Proof output
   ------------------------------------------------------------------------- *)

fun compare_string_size (s1,s2) = cpl_compare
  Int.compare String.compare ((String.size s1,s1), (String.size s2,s2))

fun compare_lemmal (lemmal1,lemmal2) =
  compare_string_size 
    (String.concatWith "|" lemmal1, String.concatWith "|" lemmal2)

fun get_status_ppsisl s = 
  let 
    val (s0,s1) = split_pair #">" s
    val sl2 = String.tokens (fn x => x = #"|") s1
    val _ = if null sl2 then raise ERR "get_status_ppsisl" "" else ()  
  in
    (s0,(hd sl2,tl sl2))
  end;
  
fun string_to_ppsisl s = 
  let 
    val (s0,s1) = split_pair #">" s
    val sl2 = 
      if s1 = "empty" 
      then [] 
      else String.tokens (fn x => x = #"|") s1
  in
    (s0,sl2)
  end
  
fun ppsisl_to_string (s,sl) = 
  s ^ ">" ^ (if null sl then "empty" else String.concatWith "|" sl)

(* -------------------------------------------------------------------------
   Merging
   ------------------------------------------------------------------------- *)

fun merge l1 l2 =
  let
    val d = ref (dempty String.compare)
    fun f (k,v) = case dfindo k (!d) of
       NONE => d := dadd k v (!d)
     | SOME oldv => if compare_lemmal (v,oldv) = LESS 
                    then d := dadd k v (!d) else ()
    val _ = app f (l1 @ l2) 
  in
    dlist (!d)
  end
  
fun merge_diff l1 l2 =
  let val setold = enew String.compare (map fst l1) in
    filter (fn (x,_) => not (emem x setold)) l2
  end
    
fun merge_simple l1 l2 = l1 @ (merge_diff l1 l2)

fun merge_soft l1 l2 = 
  let val cmp = cpl_compare String.compare (list_compare String.compare) in
    mk_fast_set cmp (l1 @ l2)
  end
  
(* -------------------------------------------------------------------------
   Proof: main functions
   ------------------------------------------------------------------------- *)

fun standard_space s = String.concatWith " " (String.tokens Char.isSpace s);

fun string_of_varconst oper =
  if is_var oper then fst (dest_var oper)
  else if is_const oper then fst (dest_const oper)
  else raise ERR "string_of_varconst" (term_to_string oper);

fun tts tm = 
  let val (oper,argl) = strip_comb tm in
    if null argl
    then string_of_varconst oper
    else "(" ^ String.concatWith " " (string_of_varconst oper :: 
         map tts argl) ^ ")"
  end 

fun human_out (s,sl) = 
  let 
    val pp = stringtag_to_pp s
    val (px1,px2) = progpair_to_progxpair_shared pp
    val tml = stringl_to_inductl pp sl
  in
    progx_to_string px1 ^ " = " ^ progx_to_string px2 ^ "\n" ^ 
    String.concatWith " | " (map tts tml)
  end


 
fun process_proofl dir l2 = 
  let
    fun log s = append_endline (dir ^ "/log") s
    fun logl l s = log (its (length l) ^ " " ^ s)
    fun is_unsat (a,(b,c)) = b = "unsat"
    fun remove_status (a,(b,c)) = (a,c)
    val l5 = map remove_status (filter is_unsat (map get_status_ppsisl l2))
    val _ = logl l5 "unsat"
    val _ = logl (filter (fn (a,c) => not (null c)) l5) 
      "unsat with at least one lemma"
    val lold = if not (exists_file (dir ^ "/previous"))
               then []
               else map string_to_ppsisl (readl (dir ^ "/previous"))
    val ldiff = merge_diff lold l5
    val lmerge = (if softmerge_flag then merge_soft lold l5 else merge lold l5)
    val _ = logl lold "previous"
    val _ = logl ldiff "diff"
    val _ = logl lmerge "current" 
    fun tonmt (key,sl) = 
      if not (!subz_flag) then map (fn x => key ^ ">" ^ x) sl else
      let 
        val pp = stringtag_to_pp key
        val tml = stringl_to_inductl pp sl
        val (_,newtml) = subz (pp,tml)
        val newsl = inductl_to_stringl pp newtml
      in
        map (fn x => key ^ ">" ^ x) newsl
      end
    val l7 = List.concat (map tonmt lmerge)
    val _ = logl l7 "examples"
  in
    writel (dir ^ "/output") l7;
    writel (dir ^ "/diff") (map ppsisl_to_string ldiff);
    writel (dir ^ "/current") (map ppsisl_to_string lmerge);
    writel (dir ^ "/diff_human") (map human_out ldiff);
    writel (dir ^ "/current_human") (map human_out lmerge)
  end
  
fun z3_prove_para expname = 
  if expname = "" then raise ERR "z3_prove_para" "empty expname" else
  let
    val expdir = selfdir ^ "/exp"
    val dir = expdir ^ "/" ^ expname
    fun log s = append_endline (dir ^ "/log") s
    fun logl l s = log (its (length l) ^ " " ^ s)
    val _ = app mkDir_err [expdir,dir]
    val l1 = readl (dir ^ "/input")
    val _ = logl l1 "targets"
    val (l2,t) = add_time 
      (parmap_sl ncore "search_term.z3_prove_ppil") (tag_job l1)
    val _ = log ("proving time: " ^ rts_round 2 t)
  in 
    process_proofl dir l2
  end

fun gen_init expname =
  let
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = app mkDir_err [selfdir ^ "/exp", dir]
    fun log s = append_endline (dir ^ "/log") s
    fun logl l s = log (its (length l) ^ " " ^ s)
    val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sem")
    val _ = logl appl "inductive problems"
    val sl = map pp_to_stringtag (map snd appl)
    val (sl2,t) = add_time 
      (parmap_sl ncore "search_term.random_inductl_string") sl
    val _ = log ("generating time: " ^ rts t) 
  in
    writel (dir ^ "/input") sl2
  end

(* -------------------------------------------------------------------------
   Initial generation of predicates
   ------------------------------------------------------------------------- *)

fun gen_prove_string s =
  let
    val _ = print_endline s
    val (jobn,pps) = split_pair #":" s
    val pp = stringtag_to_pp pps
    val _ = print_endline (human.humanf (fst pp) ^ " = " ^ 
                           human.humanf (snd pp))
    val tml = kolmo_pp pp 1024
    val il = gen_pp pp tml
  in
    z3_prove_ppil_aux (jobn,(pp,il))
  end
  
fun gen_prove_init expname =
  let
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = app mkDir_err [selfdir ^ "/exp", dir]
    fun log s = append_endline (dir ^ "/log") s
    fun logl l s = log (its (length l) ^ " " ^ s)
    val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sem")
    val _ = logl appl "inductive problems"
    val sl1 = tag_job (map pp_to_stringtag (map snd appl))
    val (sl2,t) = add_time (parmap_sl ncore "search_term.gen_prove_string") sl1
    val _ = log ("gen_prove time: " ^ rts t) 
  in
    process_proofl dir sl2
  end

(* -------------------------------------------------------------------------
   Create inference file
   ------------------------------------------------------------------------- *)

(*
load "search_term"; 
open aiLib kernel smt_hol smt_progx search_term;
val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sem");
val sl = writel (selfdir ^ "/smt_inference") 
  (map pp_to_stringtag (map snd appl));
*)

(* -------------------------------------------------------------------------
   Removing equivalent predicates (not used)
   ------------------------------------------------------------------------- *)

fun equiv_template_one a b =
  list_mk_forall ([xvar,yvar], mk_eq (a,b))

fun equiv_template a predl =
  mk_neg (list_mk_disj (map (equiv_template_one a) predl))

fun z3_prove_tml filein fileout t tml =
  let
    val cmd = z3_cmd "1" ("-t:" ^ its t) filein fileout
    val _ = write_smt filein tml
    val _ = OS.Process.system cmd
    val s = read_status fileout
    val _ = app remove_file [filein,fileout]
  in 
    s = "unsat"
  end

fun z3quotient filein fileout inductl =
  let 
    val predl = ref []
    fun loop cand = case cand of 
       [] => !predl
     | a :: m => 
       if null (!predl) then (predl := a :: !predl; loop m) else
       let val tm = equiv_template a (!predl) in
         if z3_prove_tml filein fileout 20 [tm]
         then loop m
         else (predl := a :: !predl; loop m)
       end
  in
    loop (dict_sort term_compare_size inductl)
  end

(*
load "search_term"; 
open aiLib kernel smt_hol smt_progx search_term;
val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sem");
val (a,pp) = random_elem appl;

load "search_term"; load "smlRedirect";
smlRedirect.hide_in_file (kernel.selfdir ^ "/aaa_smt16")
  search_term.gen_prove_init "smt16";


(* todo: merge all the examples from all the experiments *)
load "search_term"; 
open aiLib kernel smt_hol smt_progx search_term;
val expdir = selfdir ^ "/exp";
val l1 = map string_to_ppsisl (readl (expdir ^ "/smt5/current"));
val l2 = map string_to_ppsisl (readl (expdir ^ "/smt6/current"));
val l3 = map string_to_ppsisl (readl (expdir ^ "/smt7/current"));
val l4 = map string_to_ppsisl (readl (expdir ^ "/smt11/current"));
val l5 = merge_simple l4 (merge l3 (merge l2 l1));

fun f dir l =
  let
    val _ = mkDir_err dir
    fun g (key,sl) = map (fn x => key ^ ">" ^ x) sl
    val ldis = List.concat (map g l)
  in
    writel (dir ^ "/output") ldis;
    writel (dir ^ "/current") (map ppsisl_to_string l);
    writel (dir ^ "/current_human") (map human_out l)
  end;
  
f (selfdir ^ "/smt_rl0") l5;

*)


end (* struct *)
