(* ========================================================================= *)
(* DESCRIPTION   : Extended program datatype to store names for subloops     *)
(* ========================================================================= *)

structure qprove :> qprove = struct

open aiLib kernel sexp qsubst
val ERR = mk_HOL_ERR "qprove"

type prog = kernel.prog
type record = {intl : int list, terml: prog list, thml: prog list};
type exec = record * record -> record




val empty_record = 
  {intl = ([]: int list), 
   terml = ([]: prog list),
   thml = ([]: prog list)};

fun update_intl newintl ({intl,terml,thml}:record) = 
  ({intl = newintl,terml = terml, thml = thml}: record);

fun update_terml newterml ({intl,terml,thml}:record) = 
  ({intl = intl,terml = newterml, thml = thml}: record);

fun update_thml newthml ({intl,terml,thml}:record) = 
  ({intl = intl,terml = terml, thml = newthml}: record);

(* -------------------------------------------------------------------------
   Time limit wrapper
   ------------------------------------------------------------------------- *)

fun checktimer n (y:record) = 
  (
  abstimer := !abstimer + n; 
  if !abstimer > !timelimit then raise ProgTimeout else y
  )

fun mk_nullf n opf fl = case fl of
    [] => (fn x => checktimer n (opf (x: record * record)))
  | _ => raise ERR "mk_nullf" ""

fun mk_unf n opf fl = case fl of
    [f] => (fn x => checktimer n (opf (f x)))
  | _ => raise ERR "mk_unf" ""

fun mk_binf n opf fl = case fl of
    [f1,f2] => (fn x => checktimer n (opf (f1 x,f2 x)))
  | _ => raise ERR "mk_binf" ""

fun mk_ternf n opf fl = case fl of
   [f1,f2,f3] => (fn x => checktimer n (opf (f1 x, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf" ""

fun mk_quintf2 opf fl = case fl of
   [f1,f2,f3,f4,f5] => (fn x => checktimer 1 (opf (f1, f2, f3 x, f4 x, f5 x)))
  | _ => raise ERR "mk_quintf2" ""



(* -------------------------------------------------------------------------
   List
   ------------------------------------------------------------------------- *)

fun null_int (x:record) = update_intl [if null (#intl x) then 0 else 1] x
fun null_term (x:record) = update_intl [if null (#terml x) then 0 else 1] x
fun null_thm (x:record) = update_intl [if null (#thml x) then 0 else 1] x

fun pop_int (x:record) = case #intl x of
    a :: m => update_intl m x
  | _ => x

fun pop_term (x:record) = case #terml x of
    a :: m => update_terml m x
  | _ => x

fun pop_thm (x:record) = case #thml x of
    a :: m => update_thml m x
  | _ => x

fun push_int (x:record,y:record) = case (#intl x,#intl y) of
    (a :: m, l) => update_intl (a :: l) y
  | _ => y

fun push_term (x:record,y:record) = case (#terml x, #terml y) of
    (a :: m, l) => update_terml (a :: l) y
  | _ => y

fun push_thml (x:record,y:record) = case (#thml x, #thml y) of
    (a :: m, l) => update_thml (a :: l) y
  | _ => y

fun pushl_thml (x:record,y:record) = update_thml (#thml x @ #thml y) y

(* -------------------------------------------------------------------------
   Variable
   ------------------------------------------------------------------------- *)

val x_f = mk_nullf 1 (fn (x,y) => x)
val y_f = mk_nullf 1 (fn (x,y) => y)

(* -------------------------------------------------------------------------
   Intl
   ------------------------------------------------------------------------- *)

fun constant_int operator (x:record,y:record) = 
  update_intl [operator] empty_record;
  
fun binop_int operator (x:record, y:record) = case (#intl x, #intl y) of
    (a :: m, b :: _) => update_intl (operator (a,b) :: m) x
  | _ => x

val zero_f = mk_nullf 1 (constant_int 0)
val one_f = mk_nullf 1 (constant_int 1)
val two_f = mk_nullf 1 (constant_int 2)  
val addi_f = mk_binf 1 (binop_int (op +))
val diff_f = mk_binf 1 (binop_int (op -))
val mult_f = mk_binf 1 (binop_int (op *));

(* "arithmetic: 0,1,2,+,-,* (mod,div?)" *)

(* -------------------------------------------------------------------------
   Terml
   ------------------------------------------------------------------------- *)

val constant_tml = ["0","s","+","=","not","or"];
val var_tml = map_snd (fn x => ~x) (number_snd 1 ["x","y"]);
val constvard = dnew String.compare (number_snd 0 constant_tml @ var_tml);
fun id_of_constvar a = dfind a constvard 
   handle NotFound => raise ERR "constvard" a
fun swap_dict cmp d = dnew cmp (map swap (dlist d));
val constvarid = swap_dict Int.compare constvard;
fun constvar_of_id id = dfind id constvarid 
  handle NotFound => raise ERR "constvarid" (its id)

fun constant_tm operator (x:record,y:record) = 
  update_terml [operator] empty_record;

fun unop_tm operator (x:record) = case #terml x of
    a :: m => update_terml (operator a :: m) x
  | _ => x

fun binop_tm operator (x:record,y:record) = case (#terml x, #terml y) of
    (a :: m, b :: _) => update_terml (operator (a,b) :: m) x
  | _ => x

(* todo add type guards *)
val zerotm_f = mk_nullf 1 (constant_tm (Ins (0,[])))
fun mk_suc x = Ins (1,[x]);
val suc_f = mk_unf 1 (unop_tm mk_suc);
fun mk_add (x,y) = Ins(2,[x,y]);
val additm_f = mk_binf 1 (binop_tm mk_add);
fun mk_eq (x,y) = Ins(3,[x,y]);
val eqtm_f = mk_binf 1 (binop_tm mk_eq);
fun mk_not x = Ins(4,[x]);
val not_f = mk_unf 1 (unop_tm mk_not);

(* -------------------------------------------------------------------------
   Axioms
   ------------------------------------------------------------------------- *)
  
fun sexp_to_term sexp = case sexp of
    Atom a => Ins (id_of_constvar a, []) 
  | Sexp (Atom a :: m) => Ins (id_of_constvar a, map sexp_to_term m) 
  | Sexp _ => raise ERR "sexp_to_term" "unexpected";

val string_to_term = sexp_to_term o string_to_sexp;

val axioml_aux =
  [
  "(not (= (s x) 0))",
  "(or (not (= (s x) (s y))) (= x y))",
  "(= (+ x 0) x)",
  "(= (+ x (s y)) (s (+ x y)))"
  ];

val axioml = map string_to_term axioml_aux;

fun term_to_sexp tm = case tm of
    Ins (id,[]) => Atom (constvar_of_id id)
  | Ins (id,tml) => Sexp (Atom (constvar_of_id id) :: map term_to_sexp tml);
   
val term_to_string = sexp_to_string o term_to_sexp;

(* -------------------------------------------------------------------------
   Thml
   ------------------------------------------------------------------------- *)

exception ProofFound

val eqid = 3
val notid = 4
val falseid = 5

fun is_false (Ins(id,_)) = id = falseid
fun is_eq (Ins(id,_)) = id = eqid
fun is_not (Ins(id,_)) = id = notid
fun dest_unary (Ins(id,pl)) = 
  case pl of [p] => p 
  | _ => raise ERR "dest_unary" ""
fun dest_binary (Ins(id,pl)) = 
  case pl of [p1,p2] => (p1,p2) 
  | _ => raise ERR "dest_binary" ""

fun is_neq tm = is_not tm andalso is_eq (dest_unary tm)

(* probably this also should be counted: measure how much time
   is taken by is_contradiction *)
fun is_contradiction thm = 
  is_false thm orelse 
  (is_neq thm andalso prog_compare (dest_binary (dest_unary thm)) = EQUAL)

fun update_thml_check newthml ({intl,terml,thml}:record) = 
  if is_contradiction (hd newthml)
  then raise ProofFound
  else ({intl = intl,terml = terml, thml = newthml}: record);

fun init_conjecture cj = update_thml_check [cj] empty_record;

fun constant_thm operator (x:record,y:record) = 
  update_thml [operator] empty_record;

fun binop_thm operator (x:record,y:record) = case (#thml x, #thml y) of
    (a :: m, b :: _) => update_thml_check (operator (a,b) :: m) x
  | _ => x

fun ternop_thm operator (x:record,y:record,z:record) = 
  case (#thml x, #thml y, #thml z) of
    (a :: m, b :: _, c :: _) => update_thml_check (operator (a,b,c) :: m) x
  | _ => x


(* todo make the conjecture an input *)
val axiom_fl = map (fn x => mk_nullf 1 (constant_thm x)) axioml

(* the cost should be baked in the rewrite tactic *)
val inst_f = mk_ternf 1 (ternop_thm inst_match)
val mp_f = mk_binf 1 (binop_thm mp_match)
val rewrite_f = mk_binf 1 (binop_thm rewrite_match)


(* -------------------------------------------------------------------------
   Create executable
   ------------------------------------------------------------------------- *)

val namev = Vector.fromList (["x","y","inst","mp","rewrite"] @ 
  List.tabulate (length axiom_fl, fn i => "ax" ^ its i))
val execv = Vector.fromList ([x_f,y_f,inst_f,mp_f,rewrite_f] @ axiom_fl)

fun mk_exec_move id fl = Vector.sub (execv,id) fl 
  handle Subscript => raise ERR "mk_exec_move" (its id)
  
fun mk_exec (p as (Ins (id,pl))) = 
  let val fl = map mk_exec pl in mk_exec_move id fl end

(*
fun induct tm1 tm2 f1 f2 = 
  if not (mem (first_var tm1) (all_var tm2)) orelse 
     not (is_inductive_proof (tm2,f1,f2))
  then empty_record  
  else update_thml (clausify_negation tm2) empty_record
*)


(* 
in the brute force approach or even in any bottom-up search 
don't reevaluate if the last operation is not a loop of a theorem producing
function
*)

end (* struct *)

(* eval "2+1" = "|- 2-1 = 1" *)

(* 

fun conj_intro (a,b) = ((asm1,asm2), mk_conj (a,b))  
fun conj_elim a = 
  if not a conjuction fails 
  then 
  else 
  
fun 
  
  (every subprograms must be runnable?°



based type term list
Maybe Make it a 
elim intro
disch "term" 
undisch
elim_forall
intro_forall
elim_exist
intro_exist
          


Variable (2): x y 
Control flow (7): 
  if term_compare t1 t2 then t3 else t4
  if is_term t1 then t2 else t3
  if is_null x then t2 else t3 
  traverse loop2 (size_of_term) 
List (4): push pushl pop null
val move hyp pointer. (disch)

disch term undisch
intro elim
contrapos

elim intro (top symbol)
skolemize


Terms (7): subst, construct, destruct, or, and, not, rotate
Theorems (8):
- inst_match, mp_match, rewrite_match
- inst_unif, mp_unif, rewrite_unif
- induction (first var in term in first term), splitting on term

27 constructors.

load "qprove"; open aiLib kernel sexp qsubst qprove;
val ERR = mk_HOL_ERR "test";

val x_init = init_conjecture (string_to_term "(not (= (+ 0 0) 0))");
val y_init = empty_record;

val prog = (Ins (4,[Ins(7,[]),Ins(0,[])]));
val state = (mk_exec prog) (x_init, y_init);

val (t1,t2) = (hd (#thml r1), hd (#thml r2));
term_to_string t1;
term_to_string t2;

val t3 = rewrite_match (t1,t2);
term_to_string t3;

mk_(a,b) = 

4 loops:
loop_int x++
loop_term (traverse term)
loop2 n x and y updates
while y > 0, x and y updates.


val conjecture_f = constant_thm (!conjecture_glob)



val mk_execf = 

~P(0) \/ (P(d) /\ ~ P(d+1)) 
val (_,t) = add_time (PURE_ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM]) ([],``x=2+3``);
load "qsubst"; open qsubst;
val p1 = string_to_term "(= (+ x y) (+ y x))";

val p2 = string_to_term "(= x (+ (s (s 0)) (s (s (s 0)))))";
fun f x = rewrite_match (p1,x);
val (p3,t) = add_time (funpow 1000 f) p2;
print_endline (term_to_string p3);

goal is to have a random search working.

*)


