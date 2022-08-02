structure smt :> smt =
struct

open HolKernel Abbrev boolLib aiLib dir kernel human
val ERR = mk_HOL_ERR "smt"


(* -------------------------------------------------------------------------
   Export to SMTlib
   ------------------------------------------------------------------------- *)

val defl = ref []
fun smt prog = 
  let fun sbinop s (p1,p2) = "(" ^ s ^ " " ^ smt p1 ^ " " ^ smt p2 ^ ")" in
  case prog of
    Ins (0,[]) => "0" 
  | Ins (1,[]) => "1" 
  | Ins (2,[]) => "2" 
  | Ins (3,[p1,p2]) => sbinop "+" (p1,p2)
  | Ins (4,[p1,p2]) => sbinop "-" (p1,p2) 
  | Ins (5,[p1,p2]) => sbinop "*" (p1,p2)
  | Ins (6,[p1,p2]) => sbinop "div" (p1,p2)
  | Ins (7,[p1,p2]) => sbinop "mod" (p1,p2)
  | Ins (8,[p1,p2,p3]) => 
    "(ite (<= " ^ smt p1 ^ " 0) " ^ smt p2 ^ " " ^ smt p3 ^ ")"
  | Ins (9,[p1,p2,p3]) =>
     if depend_on_x p3 orelse depend_on_y p3 orelse
        depend_on_y p2 orelse depend_on_y p1
     then raise ERR "smt" "not supported" 
     else 
       let val (r1,r2) = (smtdef "f1" p1, smtdef "f2" p2) in
         defl := !defl @ 
         ["(forall ((n Int)) (= (f n) (ite (<= n 0) " ^ smt p3 ^ 
          " (f1 (f (- n 1))))))",
          "(forall ((x Int)) (= (g x) (f (f2 x))))"];
         "(g x)"
       end
  | Ins (10,[]) => "x"
  | Ins (11,[]) => raise ERR "smt" "not supported"
  | Ins (12,[p1,p2]) => raise ERR "smt" "not supported"
  | Ins (13,[p1,p2,p3,p4,p5]) => raise ERR "smt" "not supported"
  | _ => raise ERR "smt" (humanf prog)
  end
  
and smtdef s p = 
  let val r = smt p in
    defl := !defl @ 
      ["(declare-fun " ^ s ^ " (Int) Int)",
      "(forall ((x Int)) " ^ "(= " ^ "(" ^ s ^ " x) " ^ r ^ "))"]
  end


fun smttop s p = 
  let val _ = (defl := []; smtdef s p) in
    map (fn x => if String.isPrefix "(declare-fun" x
                 then x else "(assert " ^ x ^ ")") (!defl)
  end 

fun export_smt2_one flag dir (a,_,p1,p2) =
  let val file = dir ^ "/" ^ a ^ ".smt2" in
    writel file
    (
    ["(set-logic UFNIA)",
     "(declare-fun f (Int) Int)",
     "(declare-fun g (Int) Int)"]  @
     smttop "h1" p1 @ smttop "h2" p2 @ 
     (if flag then 
      ["(assert (exists ((c Int)) (and (>= c 0) (not (= (h1 c) (h2 c))))))"] 
      else []) @
    ["(check-sat)"]
    )
  end
  handle HOL_ERR _ => ()
  
fun export_smt2 b dir l =
  let val _ = mkDir_err dir in
    app (export_smt2_one b dir) l
  end


(* 
load "smt"; open kernel aiLib human smt;
val sl = readl "full-data5/sexpr_full";
val sl2 = map quadruple_of_list (mk_batch 4 sl);
val sl3 = map (fn (a,b,c,d) => (a,b, parse_prog c, parse_prog d)) sl2;
fun num_loops (Ins (id,pl)) = 
  (if id = 9 then 1 else 0) + sum_int (map num_loops pl);
val sl4 = filter (fn (a,b,p1,p2) => num_loops p1 + num_loops p2 <= 1) sl3;
length sl4;
export_smt2 true "smt-data-test1" sl4;
 
*)



end (* struct *)
