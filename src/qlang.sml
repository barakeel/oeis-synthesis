(* ========================================================================= *)
(* Language for the Qprover                                                  *)
(* ========================================================================= *)

structure qlang :> qlang = struct

open HolKernel Abbrev boolLib aiLib kernel qsyntax qrule sexp
val ERR = mk_HOL_ERR "qlang"

type formula = qsyntax.formula
type qprove = (formula list * (prog * int))
type state = prog list
type exec = state * state -> state 

exception Error
exception Proof
fun error () = raise Error

(* -------------------------------------------------------------------------
   Objects
   ------------------------------------------------------------------------- *)

datatype obje = Thm of formula list * int | Term of formula
type obj = obje list

fun is_thm obje = case obje of Thm _ => true | _ => false
fun mk_thmobj tml = [Thm (tml,0)];
fun dest_thmobj thm = case thm of 
    Thm (clause,_) :: _ => clause
  | _ => raise ERR "dest_thmobj" "";

fun size_obje x = case x of
    Thm (tml,_) => sum_int (map formula_size tml)
  | Term tm => formula_size tm
  
fun size_obj x = sum_int (map size_obje x)

fun hfobje x = case x of
   Thm (c,n) => (* "Thm " ^ hfc c ^ " @ " ^ its n *) hfc c
 | Term t => "Term " ^ hf t
 
fun hfobj obj = String.concatWith ", " (map hfobje obj);

val see = pe o hfobj

fun is_proof f (thml1,thml2) = (f (thml1,thml2); false) handle Proof => true

fun mk_thm tml = Thm (tml,0)
fun dest_thm thm = case thm of 
    Thm (clause,_) => clause 
  | _ => raise ERR "dest_thm" ""

(* -------------------------------------------------------------------------
   Axioms
   ------------------------------------------------------------------------- *)

val refl_ax = mk_thmobj [fh "(= x1 x1)"];
val sym_ax = mk_thmobj (map fh ["(not (= x1 x2))","(= x2 x1)"]);
val add_zero = mk_thmobj [(fh "(= (+ x1 0) x1)")];
val add_suc = mk_thmobj [fh "(= (+ x1 (suc x2)) (suc (+ x1 x2)))"];
val mult_zero = mk_thmobj [(fh "(= (* x1 0) 0)")];
val mult_suc = mk_thmobj [fh "(= (* x1 (suc x2)) (+ x1 (* x1 x2)))"];
val suc_inj = mk_thmobj (map fh ["(not (= (suc x1) (suc x2)))","(= x1 x2)"]);
val distrib = mk_thmobj [fh "(= (* x1 (+ x2 x3)) (+ (* x1 x2) (* x1 x3)))"];
val add_com = mk_thmobj [fh "(= (+ x1 x2) (+ x2 x1))"];
val mult_com = mk_thmobj [fh "(= (* x1 x2) (* x2 x1))"];
val divdiv = mk_thmobj [fh "(= (div (div x0 x1) x2) (div x0 (* x1 x2)))"]
val mult_one = mk_thmobj [fh "(= (* x0 1) x0)"]


(* -------------------------------------------------------------------------
   Simplify and check if the proof is finished
   ------------------------------------------------------------------------- *)

fun simp clause = 
  let val r = remove_diseq (remove_conflict (factor_set clause)) in
    if null r then raise Proof else r
  end

(* -------------------------------------------------------------------------
   Moving index
   ------------------------------------------------------------------------- *)

fun next_obj obj = 
  case obj of
    Thm (x,i) :: m => Thm (x,i+1) :: m
  | _ => error ()

(* -------------------------------------------------------------------------
   Paramodulate
   ------------------------------------------------------------------------- *)
   
fun find_nth acc test n l = case l of 
    [] => NONE
  | a :: m => 
    if not (test a) then find_nth (a :: acc) test n m else
    if n <= 0 then SOME (a,rev acc @ m) else find_nth (a :: acc) test (n-1) m

fun paramodulate_obj obj1 obj2 =
  case (obj1,obj2) of
    (Thm (clause1,i1) :: _, Thm(clause2,i2) :: m2) => 
    (
    case find_nth [] is_eq i1 clause1 of 
      SOME (A ((0,3),[red,res]),clause1') => 
      (
      dbg 2 (fn () => "rw: " ^ hf red ^ " , " ^ hf res);
      case paramodulate clause1' (red,res) (clause2,i2) of
        SOME newclause => 
        let val r = simp newclause in 
          dbg 1 (fn () => "rw: " ^ hfc r);
          Thm (r, 0) :: m2
        end
      | NONE =>
        (
        dbg 1 (fn () => "rw: identity");
        obj2
        )
      )
      | _ => error ()
    )
  | _ => error ()

(* -------------------------------------------------------------------------
   Resolve
   ------------------------------------------------------------------------- *)

fun resolve_obj obj1 obj2 = case (obj1,obj2) of
    (Thm (clause1,_) :: _, Thm thm2 :: m2) => 
    (
    case resolve clause1 thm2 of
      SOME newclause => Thm (simp newclause, 0) :: m2
    | NONE => obj2
    )
  | _ => error ()

(* -------------------------------------------------------------------------
   Factor
   -------------------------------------------------------------------------*) 

fun factor_obj obj = case obj of
    Thm thm :: m => 
    (case factor thm of NONE => obj | SOME newclause =>
     Thm (simp newclause, 0) :: m)
  | _ => error ()

(* -------------------------------------------------------------------------
   Control flow
   ------------------------------------------------------------------------- *)

fun varx (x,y) = x

fun vary (x,y) = y

fun cond x f1 f2 = if null x then f2 () else f1 ()

fun while2 f g x y =
  if null x then y else while2 f g (f (x,y)) (g (x,y))

fun repeat f x =
  let val y = f x in
    if PolyML.pointerEq (x,y) orelse x = y then x else repeat f y
  end

fun eq_obj x y = 
  if PolyML.pointerEq (x,y) then y else
  (
  case (x,y) of
    (Thm (thm1,_) :: _, Thm (thm2,_) :: _)  => 
    if list_compare formula_compare (thm1,thm2) = EQUAL then y else []
  | (Term t1 :: _ , Term t2 :: _) =>  
    if formula_compare (t1,t2) = EQUAL then y else []
  | _ => []
  )
  
(* -------------------------------------------------------------------------
   List operations
   ------------------------------------------------------------------------- *)
 
fun hd_obj a = case a of e :: m => [e] | _ => error ()
fun tl_obj a = case a of e :: m => m | _ => error ()
fun push_obj a b = (checktimern (length a); a @ b)
val null_obj = []

(* -------------------------------------------------------------------------
   Term operations
   ------------------------------------------------------------------------- *)

fun same_id x y = case (x,y) of
     (Thm _ :: _, Thm _ :: _)  => y
   | (Term (A (i1,_)) :: _ , Term (A (i2,_)) :: _ ) => 
     if i1 = i2 then y else []
   | _ => []

fun is_var x = case x of
    Term (A(i,_)) :: _ => if is_varid i then x else []
  | _ => []

fun is_not x = case x of
    Term (A(i,_)) :: _ => if i = not_id then x else []
  | _ => []

fun is_eq x = case x of
    Term (A(i,_)) :: _ => if i = eq_id then x else []
  | _ => []

fun is_add x = case x of
    Term (A(i,_)) :: _ => if i = add_id then x else []
  | _ => []

fun dest x = case x of
    Thm (tml,_) :: m => map Term tml @ m
  | Term (A(_,tml)) :: m => map Term tml @ m
  | [] => error ()

(* -------------------------------------------------------------------------
   Induction
   ------------------------------------------------------------------------- *)

(* looks for skolems with no arguments *)
fun nth_skoleml n skd pl = case pl of [] => NONE | p :: m => 
  (
  case nth_skolem n skd p of 
     SOME id => SOME id 
   | NONE => nth_skoleml n skd m
  )

and nth_skolem n skd (A(id,pl)) =
  if is_skolemid id andalso null pl then 
    if emem id (!skd) then nth_skoleml n skd pl else
    if elength (!skd) >= n then SOME id else
    (skd := eadd id (!skd); nth_skoleml n skd pl)
  else nth_skoleml n skd pl  

fun nth_skoleml n skd pl = case pl of [] => NONE | p :: m => 
  (
  case nth_skolem n skd p of 
     SOME id => SOME id 
   | NONE => nth_skoleml n skd m
  )

fun nth_skolem_thml n skd thml = case thml of [] => NONE | thm :: m => 
  (
  case nth_skoleml n skd (dest_thm thm) of 
    NONE => nth_skolem_thml n skd m 
  | SOME id => SOME id
  )

fun subst_one_litl (id,tm) litl = map (subst_one (id,tm)) litl
fun subst_one_thm (id,tm) thm = Thm (subst_one_litl (id,tm) (dest_thm thm), 0)

fun negate_thml thml = 
  let 
    val clausel1 = map (map neg o dest_thm) thml 
    val clausel2 = cartesian_productl clausel1
  in
    map mk_thm clausel2
  end


(*
~P(oldsk)
~P(0)
~(!x.P(x) => P(x+1)): ?x. P(x) /\ ~P(x+1): P(sk) ~P(sk+1)
*)

fun induct_obj f obj =
  let 
    val _ = dbg 1 (fn () => "induction: " ^ hfobj obj)
    val thml = filter is_thm obj
    val n = case thml of Thm (_,n) :: _ => n | _ => error ()
    val skold = case nth_skolem_thml n (ref (eempty id_compare)) thml of
      NONE => error () 
    | SOME x => x
    val zero = A((1,0),[])
    val p0 = map (subst_one_thm (skold,zero)) thml
    val _ = dbg 2 (fn () => "base case: " ^ hfobj p0)
    val sk = A(fresh_skolemid (),[])
    val psk = map (subst_one_thm (skold,sk)) thml
    val _ = dbg 2 (fn () => "inductive hypothesis: " ^ hfobj psk)
    val pssk = negate_thml (map (subst_one_thm (skold, mk_add (sk,one))) thml)
    val _ = dbg 2 (fn () => "inductive consequent: " ^ hfobj pssk)
  in
    if is_proof f (p0,[]) then pssk @ psk else error ()
  end

fun induct_obji obj =
  let 
    val _ = dbg 1 (fn () => "induction: " ^ hfobj obj)
    val thml = filter is_thm obj
    val n = case thml of Thm (_,n) :: _ => n | _ => error ()
    val skold = case nth_skolem_thml n (ref (eempty id_compare)) thml of
      NONE => error () 
    | SOME x => x
    val zero = A((1,0),[])
    val p0 = map (subst_one_thm (skold,zero)) thml
    val _ = dbg 2 (fn () => "base case: " ^ hfobj p0)
    val sk = A(fresh_skolemid (),[])
    val psk = negate_thml (map (subst_one_thm (skold,sk)) thml)
    val _ = dbg 2 (fn () => "inductive hypothesis: " ^ hfobj psk)
    val pssk = map (subst_one_thm (skold, mk_add (sk,one))) thml
    val _ = dbg 2 (fn () => "inductive consequent: " ^ hfobj pssk)
  in
    (p0, pssk @ psk)
  end

(* -------------------------------------------------------------------------
   Conjecturing
   ------------------------------------------------------------------------- *)

fun conjecture_obj f thm = case thm of
    Term tm :: m =>
    (
    if not (is_boolean tm) then error () else
    let 
      val _ = dbg 1 (fn () => "conjecture: " ^ hf tm) 
      val obj = map mk_thm (CNF (neg tm)) 
    in
      if is_proof f (obj,[]) then obj @ m else error ()
    end
    )
  | _ => error ()
  
(* -------------------------------------------------------------------------
   Polynomial normalization
   ------------------------------------------------------------------------- *)

fun add_poly (p1,p2) = 
  (
  incr abstimer;
  case (p1,p2) of
    ([], p) => p
  | (p, []) => p
  | ((m1,c1) :: ms1, (m2,c2):: ms2) =>
    (
    case list_compare formula_compare (m1,m2) of
      EQUAL =>
      let val c = c1 + c2 in
        if c = 0 then add_poly (ms1, ms2)
        else (m1, c) :: add_poly (ms1, ms2)
      end
    | LESS => (m1, c1) :: add_poly (ms1, p2)
    | GREATER => (m2, c2) :: add_poly (p1, ms2)
    )
  )
     
fun merge_mono l1 l2 = 
  (
  incr abstimer;
  case (l1,l2) of
     (l, []) => l
  | ([], l) => l
  | (a1 :: m1, a2 :: m2) => 
    (
    case formula_compare (a1,a2) of
      EQUAL => a1 :: a2 :: merge_mono m1 m2
    | LESS => a1 :: merge_mono m1 l2
    | GREATER => a2 :: merge_mono l1 m2
    )
  )
  
fun mult_mono (m1,c1) (m2,c2) = (merge_mono m1 m2, c1 * c2)

fun mult_mono_poly m p = map (mult_mono m) p;

fun mult_poly (p1,p2) = case p1 of
    [] => []
  | m :: ms => add_poly (mult_mono_poly m p2, mult_poly (ms,p2));
  
(* todo normalize inner part first *)
fun formula_to_poly p = case p of
(*  A ((0,4),[]) => []
  | A ((0,5),[p]) => add_poly (formula_to_poly p, [([],1)])
  | *) 
    A ((0,6),[p1,p2]) => add_poly (formula_to_poly p1, formula_to_poly p2) 
  | A ((0,7),[p1,p2]) => mult_poly (formula_to_poly p1, formula_to_poly p2)
  | A ((1,x),[]) => [([],x)]
  | _ => [([p],1)];


fun mono_to_formula1 xl = case xl of
    [] => raise ERR "mono_to_formula1" ""
  | [x] => x
  | x :: m => A (mult_id, [x, mono_to_formula1 m]) 

fun mono_to_formulac (xl,coeff) = case xl of
    [] => A ((1,coeff),[])
  | x :: m => A (mult_id, [x, mono_to_formulac (m,coeff)]) 
  
fun mono_to_formula (xl,coeff) =
  if coeff = 1 then 
    if null xl then A((1,1),[]) else mono_to_formula1 xl
  else mono_to_formulac (xl,coeff)
  
fun poly_to_formula poly = case poly of
    [] => A ((1,0), [])
  | [mono] => mono_to_formula mono
  | mono :: m => A (add_id, [mono_to_formula mono, poly_to_formula m])

fun norm_poly_one formula = poly_to_formula 
  (filter (fn x => snd x <> 0) (formula_to_poly formula))

fun norm_poly (A(id,argl)) = 
  if id = add_id orelse id = mult_id
  then norm_poly_one (A(id, map norm_poly_done argl))
  else A(id, map norm_poly argl)
   
and norm_poly_done (A(id,argl)) =
  if id = add_id orelse id = mult_id
  then A(id, map norm_poly_done argl)
  else A(id, map norm_poly argl) 
   
fun norm_poly_obj obj = 
  (
  dbg 1 (fn () => "norm: " ^ hfobj obj);
  case obj of
    Thm (clause,_) :: m => Thm (simp (map norm_poly clause), 0) :: m
  | _ => error () 
  )
  
(* -------------------------------------------------------------------------
   Parsing the conjecture
   ------------------------------------------------------------------------- *)  
  
fun rename sexp = case sexp of
    Atom "*" => Atom "."
  | Atom "x" => Atom "x0"
  | Atom x => Atom x
  | Sexp l => Sexp (map rename l);

fun find_body e = case e of
    Sexp [Atom "assert",Sexp [Atom "forall",_,Sexp [Atom "=",_,body]]]
     => SOME body
  | _ => NONE;

fun conjecture_of dir pbs = 
  let
    val l1 = smt_hol.read_smt_sexp (dir ^ "/" ^ pbs);
    val l2 = List.mapPartial find_body l1;
    val (s1,s2) = pair_of_list (map (sexp_to_string o rename) l2)
  in
    "(forall x0 (= " ^ s1 ^ " "  ^ s2 ^ "))"
  end
  handle HOL_ERR {message = s, ...} => raise (ERR pbs s);

(* -------------------------------------------------------------------------
   Parsing the conjecture
   ------------------------------------------------------------------------- *)

fun is_num (A(id,_)) = fst id = 1
fun dest_num (A(id,_)) = snd id

(*
val zero_id = (1,0)
val add_id = (0,6)
val mult_id = (0,7)
val diff_id = (0,8)
val div_id = (0,9)
val mod_id = (0,10)
val cond_id = (0,11)
val loop_id = (0,12)
val compr_id = (0,13)
val loop2_id = (0,14)
*)

val binv = Vector.fromList 
  (
  List.tabulate (6, fn i => (fn _ => raise ERR "binv" (its i))) @ 
  [op +, op *, op -, op div, op mod]
  )

fun eval p = case p of
    A(id,[a,b]) => 
    if id = eq_id then A(id, map eval [a,b]) else
    let 
      val (a',b') = (eval a, eval b)
      val oper = Vector.sub (binv, snd id)  
    in
      if is_num a' andalso is_num b' 
      then A((1,oper (dest_num a', dest_num b')),[])
      else A((0,6),[a',b'])
    end
  | A(id,pl) => A(id, map eval pl)


end (* struct *)

(* -------------------------------------------------------------------------
   Problems from the benchmark (manual)
   ------------------------------------------------------------------------- *) 
   
   
   
(*
load "qlang"; load "human"; load "smt_progx"; load "smt_hol"; 
open aiLib kernel qsyntax qrule qlang;
open aiLib sexp ;
val ERR = mk_HOL_ERR "test";
val _ = infix_flag := true;

val appl = smt_progx.read_anumprogpairs "smt_benchmark_progpairs";

fun contain l (Ins(id,argl)) = mem id l orelse exists (contain l) argl;
fun contain_app l (a,(p1,p2)) = contain l p1 orelse contain l p2;

(* -------------------------------------------------------------------------
   Instructions:
   0 1 2 3 4 5 6 7 8    9  10 11 12    13    14   15
   A B C D E F G H I    J    K L M     N     O    P
   0 1 2 + - * / % cond loop x y compr loop2 push pop
   ------------------------------------------------------------------------- *)
   
val avoidl = [4,6,7,8,12];
val (appl1,appl2) = partition (contain_app avoidl) appl;
length appl1; length appl2;
val avoidl = [13,14];
val (appl2a,appl2b) = partition (contain_app avoidl) appl2;
length appl2a; length appl2b;

fun pplen (a,(p1,p2)) = prog_size p1 + prog_size p2;

val appl3 = dict_sort compare_imin (map_assoc pplen appl2a);


fun f x =
  let val ((a,(p1,p2)),n) = List.nth (appl3,x) in
    pe (human.humanf p1);
    pe (human.humanf p2)
  end;

fun g x =
  let 
    val ((a,(p1,p2)),n) = List.nth (appl3,x)
    val r = mk_eq (prog_to_formula p1, prog_to_formula p2) 
  in
    r
  end;

val x = g 10; hf x;
val y = eval x; hf y;
val y = subst_one ((3,0),zero) x; hf y;
val y1 = subst_one ((3,0),mk_var 0) x; hf y1;
val y2 = subst_one ((3,0),mk_add (mk_var 0,one)) x; hf y2;


(* evaluate: transforms ground formulas back into a program
   and evaluate them on 0,0 *)


val y = norm_poly_obj x; see y;

(* todo: create an induct tactic *)



a0 = 2
b0 = 2
a1 = 4
b1 = 2
a2 = 6
b1 = 4
by offset induction 

by offset
a0 = 1
b0 = x0
a1 = 1 + x0
b1 = 1

a0 = 1 + x0
b0 = 1

by finite expansion
(loop2 ((1 + x) * (x + y)) x 2 x 0)
((1 + ((x * x) + x)) * ((2 + x) * x))


10^n*n!
(loop (2 * ((1 + (2 + 2)) * (x * y))) x 1)

((loop (x * y) x 1) * (loop2 (x * y) y x 1 (2 + (2 * (2 + 2)))))
n! * 10^n


b1 = a0


(loop (loop (x + x) y x) x 2)

x*2^y

a0 = 2
a1 = 2 * 2^1
a2 = 4 * 2^2
a3=  8 * 2^3
etc

2^ (triangular) 



(loop2 (x * y) (y + y) x 2 2)





a0 = 2 = 1 
a1 = 2*2 = 2
a2 = 4*4 = 4
a3 = 16*8 = 7
a4 = 7+4 = 11
a5 = 11+5 = 16


an = a_n-1 * 2^(n-1)
bn = 2^n

loop2 y 0 x 1 2

a(0) = 1
b(0) = 2
a(n+1) = b(n)
b(n+1) = 0

a(1) = 2
b(1) = 0

a(2) = 0
b(2) = 0

1200000

(if x <= 0 then 1 else 2)

(loop (loop 1 x 2) (2 - x) 0)

loop (if x <= 0 then 2 else 1) (2-x) 0

a(x) = 0 if x <= 0
a(x) = 2
a(x) = 1 if x >= 2
....
a(2-0) = a(2) = 2
a(2-1) = a(1) = 1
a(2-x) = 0 if 2-x <= 0




val cjl = map (fh o conjecture_of "smt_sub") sl;

(* random_elem sl; *)

fun contain_largeid (A(id,l)) = 
  (fst id = 0 andalso snd id > 7) orelse exists contain_largeid l;

val cjl1 = filter (not o contain_largeid) cjl;

fun is_true cj = 
  ((norm_poly_obj (map mk_thm (CNF (neg cj)))); false)
  handle Proof => true;

val (sltrue,slfalse) = partition is_true cjl1; length sltrue; length slfalse;

map hf slfalse;


fh cj 
val cj = conjecture_of "A108589_2";
val t0 = map mk_thm (CNF (neg (fh cj))); see t0;
val t1 = rw divdiv t0; see t0;
val t2 = norm_poly_obj t1;

val pbs = "A292740_1";
val cj = conjecture_of pbs;
val t1 = norm_poly_obj t0;

val pbs = "A64995_6";
val cj = conjecture_of pbs;
val t0 = map mk_thm (CNF (neg (fh cj))); see t0;
val t1 = norm_poly_obj t0; see t1;
val t2 = repeat (rw mult_one) t1; see t2;
val t3 = repeat (rw divdiv) t2; see t3;
val t4 = repeat (rw mult_one) (norm_poly_obj t3); see t4;
val t5 = repeat (rw divdiv) t4; see t5;
*)

(* -------------------------------------------------------------------------
   Problems from the benchmark (auto)
   ------------------------------------------------------------------------- *) 

(*
load "qlang"; open aiLib kernel qsyntax qrule qlang;
load "smt_hol"; open aiLib sexp ;
val ERR = mk_HOL_ERR "test";



val sl = listDir (selfdir ^ "/smt_subnoloop");
val cjl = map conjecture_of sl;
fun is_true cj = 
  let val cj = conjecture_of pbs in
    (norm_poly_obj (map mk_thm (CNF (neg cj))); false)
    handle Proof => true
  end;
val (sltrue,slfalse) = partition is_true sl; length sltrue; length sl;
val pbs = random_elem slfalse; (* A108589_2 *)

val rw = paramodulate_obj;
val mp = resolve_obj;
val sl = listDir (selfdir ^ "/smt_subnoloop");
val pbs = random_elem sl; 
val cj = conjecture_of "A108589_2";
val t0 = map mk_thm (CNF (neg (fh cj))); see t0;
val t1 = rw 
val t1 = norm_poly_obj t0; see t1;

val pbs = "A292740_1";
val cj = conjecture_of pbs;






val t0 = map mk_thm (CNF (neg (fh conjecture))); see t0;
val t1 = repeat (rw distrib) t0; see t1;
val t2 = repeat (rw mult_suc) t1; see t2;
(* todo make it faster and smarter *)
*)


(* -------------------------------------------------------------------------
   Commutativity of addition
   ------------------------------------------------------------------------- *)  

(*
load "qlang"; open aiLib kernel qsyntax qrule qlang;
val ERR = mk_HOL_ERR "test";

dbg_flag := true;
dbg_level := 1;
PolyML.print_depth 0;
val rw = paramodulate_obj;
val mp = resolve_obj;

(* x + y = y + x *)
val conjecture = fh "(forall x1 (forall x2 (= (+ x1 x2) (+ x2 x1))))";
val t0 = map mk_thm (CNF (neg conjecture)); see t0;
val (t1,t2) = induct_obji t0;
(* base case *)
val (t3,t4) = induct_obji t1;
val _ = rw refl_ax t3;
val t5 = rw add_suc t4; see t5;
val t6 = rw (tl t5) t5; see t6;
val _ = rw add_zero (rw add_zero t6);
(* inductive case *)
val t3 = rw add_suc t2; see t3;
val t4 = mp sym_ax (tl t2); see t4;
val t5 = rw t4 t3; see t5;
val (t6,t7) = induct_obji (next_obj [hd t5]);
val t8 = rw add_zero (rw add_zero t6);
val t9 = rw add_suc t7; see t9;
val t10 = rw (tl t9) t9; see t10;
val _ = rw add_suc t10;
*)


 
 


