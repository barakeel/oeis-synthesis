
load "kernel"; open aiLib kernel;

(*
## variable are nonpositive integers
## constants are positive integers

### term primitives
dest_ins tml 
mk_ins tml
term_eq tml1 tml2
term_comp 
is_inst tm1 tm2
subst tm1 tm2 tm3


### theorem primitives
rewrite thm1 thm2
rewritel thml1 thm2

induct on "nth" skolem. (modulo)

todo: rewrite on "nth" occurence. (modulo))
rewrite_unify
mp_unify
inst_unify
inst_tml


conjecture (term): term \/ ~term
induct_tac (base_case_tac,inductive_case_tac)


A \/ B (disjunct variables)
A

val thml = cut (term, proof) -> thm list

~A, B
(* do a minimal project with just rewrite and equality 
and a conjecture
*)

*)
fun clausify_term term = term

type record = 
  {intl : int list, 
   terml: prog list,
   thml: prog list};

val empty_record = 
  {intl = ([]: int list), 
   terml = ([]: prog list),
   thml = ([]: prog list)};

fun start_record term = 
  {intl = ([]: int list), 
   terml = ([]: prog list),
   thml = ([]: prog list)};

fun checktimer y = 
  (incr abstimer; if !abstimer > !timelimit then raise ProgTimeout else y)
 
(* -------------------------------------------------------------------------
   Intl
   ------------------------------------------------------------------------- *)

fun update_intl newintl ({intl,terml,thml,goall}:record) = 
  ({intl = newintl,terml = terml, thml = thml, goall = goall}: record);

fun constant_int operator = update_intl [operator] empty_record

fun binop_int operator (x:record) (y:record) = case (#intl x, #intl y) of
    (a :: m, b :: _) => update_intl (operator (a,b) :: m) x
  | _ => x

(* "arithmetic: 0,1,2,+,-,* (mod,div?)" *)

(* -------------------------------------------------------------------------
   Terml
   ------------------------------------------------------------------------- *)

fun update_terml newterml ({intl,terml,thml,goall}:record) = 
  ({intl = intl,terml = newterml, thml = thml, goall = goall}: record);

fun constant_tm operator = update_terml [operator] empty_record;

fun binop_term operator (x:record) (y:record) = case (#terml x, #terml y) of
    (a :: m, b :: _) => update_terml (operator (a,b) :: m) x
  | _ => x
  
(* -------------------------------------------------------------------------
   Thml
   ------------------------------------------------------------------------- *)

fun update_thml newthml ({intl,terml,thml,goall}:record) = 
  ({intl = intl,terml = terml, thml = newthml, goall = goall}: record);

fun constant_thm operator = update_thml [operator] empty_record;

fun binop_thm operator (x:record) (y:record) = case (#thml x, #thml y) of
    (a :: m, b :: _) => update_thml (operator (a,b) :: m) x
  | _ => x



(* maybe should be goal list list *)

(* uses the global substa array *)


(* use eval_conversion to evaluate ground terms such as eval "2+1" = "|- 2-1 = 1" *)
(* ~P(0) \/ (P(d) /\ ~ P(d+1)) *)





val axioml =
  [
  "(not (= (s x) 0))",
  "(or (not (= (s a) (s b))) (= a b))",
  "(= (s (p x)) x)",
  "(= (p (s x)) x)",
  "(= (+ a 0) a)",
  "(= (+ a (s b) (s (+ a b))",
  "(= (+ a (p b) (p (+ a b))",
  "(= (+ a (- a)) 0)"
  ]


  [
  "(= (+ a b) (+ b a))", (* commutativity *)
  "(= (+ (+ a b) c) (+ a (+ b c)))", (* associativity *)
  ]

val axioml =
  [
  (* addition *)
  "(= (+ a 0) a)",
  "(= (+ a b) (+ b a))", (* commutativity *)
  "(= (+ (+ a b) c) (+ a (+ b c)))", (* associativity *)
  "(= (+ a (- a)) 0)", (* inverse *)
  "(= (- (- a)) a)",
  (* multiplication *)
  "(= (* a 0) 0)",
  "(= (* a 1) a)",
  "(= (* a b) (* b a))", (* commutativity *)
  "(= (* (* a b) c) (* a (* b c)))", (* associativity *)
  "(= (* a (+ b c)) (+ (* a b) (* a c)))", (* distributivity *)
  "(= (* a (- b)) (* (- a) b))",
  "(= (- (* a b)) (* a (- b)))",
  (* equality *)
  "(=> (= a b) (= b a))"
  ]

(* congruence *)

(* mod and div *)
(*
(a div b) = ((a - b) div b) + 1
(a div b) = ((a + b) div b) - 1

(a mod b) = (a - b) mod b
(a mod b) = (a + b) mod b
*)





(*    
val v3 = Ins(~3,[]);
val c0 = Ins(0,[]);
val r = match v3 c0;
sub_glob;
val p = inst (Ins(2,[v3,v3]));

clean_dirty ();
sub_glob;


axioml (might be a list or vector)
defl (list)
acting on variables. 

rewrite (a,b) rewrite the top element of b with the list a.
rewrite
apply (a,b) apply the top element of b to the list a.
(sym thm)

induction:




*)

