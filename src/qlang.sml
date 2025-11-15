(* ========================================================================= *)
(* Language for the Qprover                                                  *)
(* ========================================================================= *)

structure qlang :> qlang = struct

open HolKernel Abbrev boolLib aiLib kernel qsyntax qrule
val ERR = mk_HOL_ERR "qlang"

type prog = kernel.prog
type formula = kernel.prog
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

fun mk_thm tml = [Thm (tml,0)];
fun dest_thm thm = case thm of 
    Thm (clause,_) :: _ => clause
  | _ => raise ERR "dest_thm" "";

fun size_obje x = case x of
    Thm (tml,_) => sum_int (map prog_size tml)
  | Term tm => prog_size tm
  
fun size_obj x = sum_int (map size_obje x)

(* -------------------------------------------------------------------------
   Axioms
   ------------------------------------------------------------------------- *)

val refl_ax = mk_thm [fh "(= x1 x1)"];
val sym_ax = mk_thm (map fh ["(not (= x1 x2))","(= x2 x1)"]);
val peano1 = mk_thm [(fh "(= (+ x1 0) x1)")];
val peano2 = mk_thm [fh "(= (+ x1 (suc x2)) (suc (+ x1 x2)))"];

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
      SOME (Ins (3,[red,res]),clause1') => 
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

fun eq_obj x y = 
  if PolyML.pointerEq (x,y) then y else
  (
  case (x,y) of
    (Thm (thm1,_) :: _, Thm (thm2,_) :: _)  => 
    if list_compare prog_compare (thm1,thm2) = EQUAL then y else []
  | (Term t1 :: _ , Term t2 :: _) =>  
    if prog_compare (t1,t2) = EQUAL then y else []
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
   | (Term (Ins (i1,_)) :: _ , Term (Ins (i2,_)) :: _ ) => 
     if i1 = i2 then y else []
   | _ => []

fun is_var x = case x of
    Term (Ins(i,_)) :: _ => if i < 0 then x else []
  | _ => []

fun is_not x = case x of
    Term (Ins(i,_)) :: _ => if i = not_id then x else []
  | _ => []

fun is_eq x = case x of
    Term (Ins(i,_)) :: _ => if i = eq_id then x else []
  | _ => []

fun is_zero x = case x of
    Term (Ins(i,_)) :: _ => if i = zero_id then x else []
  | _ => []

fun is_suc x = case x of
    Term (Ins(i,_)) :: _ => if i = suc_id then x else []
  | _ => []

fun is_add x = case x of
    Term (Ins(i,_)) :: _ => if i = add_id then x else []
  | _ => []

fun dest x = case x of
    Thm (tml,_) :: m => map Term tml @ m
  | Term (Ins(_,tml)) :: m => map Term tml @ m
  | [] => error ()


(* -------------------------------------------------------------------------
   Derived functions constructed from primitive ones
   ------------------------------------------------------------------------- *)





end (* struct *)

(*
load "qlang"; open aiLib kernel qsyntax qsubst qlang;
val ERR = mk_HOL_ERR "test";

val rw = paramodulate_obj;
val rws = paramodulate_sym_obj;

val conjecture = mk_thm [fh "(not (= (+ 10 13) 23))"];

fun f x y = cond (eq_obj x y) (fn () => x) (fn () => empty_obj);
fun g (x:obj) y = rw axiom1 (rw axiom2 y);

dbg_flag := true;
dbg_level := 1;
PolyML.print_depth 10;
val r0 = while2 f g axiom1 conjecture; (17 tokens)
*)


 
 


