load "qlang"; load "human"; load "smt_progx"; load "smt_hol";
open aiLib kernel qsyntax qrule qlang sexp;
val ERR = mk_HOL_ERR "test";
val pbl = map_snd (fn x => (abstimer := 0; aall poly x)) (get_problems ());
val _ = infix_flag := true;
val _ = x_flag := true;
val _ = abstimer := 0;

val (anum,gl) = List.nth (pbl,0); init_proof gl;
val proof1 = ac decouple >> induct2 >> auto >> refl >>
 (ac unfold) >> (replace_asm 2 o replace_asm 1) >> refl >>
 (ac unfold) >> (replace_asm 2 o replace_asm 1) >> refl;
val (pbl1,pbl2) = partition (test_pb proof1) pbl; length pbl1; (* 62 *)

val (anum,gl) = List.nth (pbl2,4); init_proof gl;
val proof2 = ac decouple >> induct >> auto >> refl >>
 ac unfold >> replace_asm 1 >> ac (replace_atl constant_loop2h) >>
 refl;
val (pbl5,pbl6) = partition (test_pb proof2) pbl2; length pbl5; (* 43 *)

val (anum,gl) = List.nth (pbl6,0); init_proof gl;
val proof4 = induct >> auto >> refl >>
  ac unfold >> replace_asm 1 >> ac gen_idloop >> drop_asm >> induct >>
  repeat (ac unfold) >> refl >>
  ac unfold >> replace_asm 1 >> refl;
val (pbl7,pbl8) = partition (test_pb proof4) pbl6; length pbl7; (* 2 *)

val (anum,gl) = List.nth (pbl8,0); init_proof gl;
val proof5 = induct2_2 >> auto >> refl >> auto >> refl >>
  ac unfold >> ac (lhf unfold) >> apply_asmk 2 (lhf unfold) >>
  addzero_asmk_left 2 >> replace_asm 1 >> ac (rhf (argf 1 unfold)) >> refl;
val (pbl9,pbl10) = partition (test_pb proof5) pbl8; length pbl9; (* 17 *)

val (anum,gl) = List.nth (pbl10,0); init_proof gl;
val proof6 = auto >> refl;
val (pbl11,pbl12) = partition (test_pb proof6) pbl10; length pbl11; (* 618 *)

val (anum,gl) = List.nth (pbl12,0); init_proof gl;
val proof7 = induct >> auto >> refl >> 
  ac unfold >> replace_asm 1 >> ac gen_idloop >> drop_asm >> induct >>
  auto >> refl >> apply_asm simp >> ac unfold >> replace_asm 1 >> refl;
val (pbl13,pbl14) = partition (test_pb proof7) pbl12; length pbl13; (* 10 *)

val (anum,gl) = List.nth (pbl14,0); init_proof gl;
val proof8 = induct >> auto >> refl >> ac unfold >> ac 
  (lhf unfold) >> replace_asm 1 >> ac (replace_atl constant_loop2h) >> refl;
val (pbl15,pbl16) = partition (test_pb proof8) pbl14; length pbl15; (* 3 *)

fun replace_asm_sym n gl = case gl of
    [] => raise Proof
  | (asm,w) :: m =>
    let val (a,b) = dest_eq (List.nth (asm,n)) in
      (asm, replace (b,a) w) :: m
    end;
fun swap n = substl [((3,0),mk_var 1),((3,n),mk_var 0)];

val (anum,gl) = List.nth (pbl16,0); init_proof gl;
val proof9 = 
  ac simp >> induct2_2 >> auto >> refl >> ac (eqf eval) >> refl >>
  ac unfold >> ac (rhf (argf 1 unfold)) >> ac (lhf (argf 1 unfold)) >>
  replace_asm 1 >> drop_asm >> ac gen_idloop >> ac (swap 1) >> induct >> 
  ac (eqf eval) >> refl >>
  ac (rhf unfold) >> ac (lhf (argf 1 unfold)) >> replace_asm_sym 1 >> 
  drop_asm >> ac gen_idloop >> ac (swap 2) >> induct >> auto >> refl >>
  ac unfold >> ac (lhf unfold) >> replace_asm 1 >> refl;
  
val (pbl17,pbl18) = partition (test_pb proof9) pbl16; length pbl17; (* 1 *)

val (anum,gl) = List.nth (pbl18,0); init_proof gl;
val proof10 = imitate >> auto >> refl >> auto >> refl >>
  induct >> auto >> refl >>
  ac unfold >> ac (replace_atl constant_loop2h) >> replace_asm 1 >> refl;

val (pbl19,pbl20) = partition (test_pb proof10) pbl18; length pbl19;  (* 2 *)

val (anum,gl) = List.nth (pbl20,0); init_proof gl;
val proof11  = ac simp >> induct2 >> 
  auto >> refl >> 
  ac unfold >> replace_asm 1 >> replace_asm 2 >> refl >>
  ac unfold >> replace_asm 1 >> replace_asm 2 >> refl;
val (pbl21,pbl22) = partition (test_pb proof11) pbl20; length pbl21; (* 10 *)

val (anum,gl) = List.nth (pbl22,0); init_proof gl;

val proof12 = induct2_2 >> auto >> refl >> auto >> refl >> 
  ac unfold >> ac (lhf (argf 1 (argf 1 unfold))) >> ac (rhf (argf 1 unfold)) 
  >> replace_asm_sym 1 >> replace_asm_sym 2 >> refl;
val (pbl23,pbl24) = partition (test_pb proof12) pbl22; length pbl23; (* 14 *)

val (anum,gl) = List.nth (pbl24,0); init_proof gl;

val proof13 = ac decouple >> induct >> auto >> refl >>
  ac unfold >> ac (lhf unfold) >> ac (replace_atl constant_loop2h) >> 
  replace_asm 1 >> refl;
  
val (pbl25,pbl26) = partition (test_pb proof13) pbl24; length pbl25; (* 8 *)

val (anum,gl) = List.nth (pbl26,0); init_proof gl;

val proof14 = repeat (ac (lhf (argf 0 unfold))) >> induct >> auto >> refl >>
  ac unfold >> ac (replace_atl constant_loop2h) >> replace_asm 1 >> refl;
val (pbl27,pbl28) = partition (test_pb proof14) pbl26; length pbl27; (* 46 *)

(*
load "qscript";

fun add_eq_sym eq formula  = 
  let val (a,b) = dest_eq eq in
    mk_add (formula, mk_diff (b,a))
  end;

fun find_loop2h p = case p of
    A ((0,16),_) => SOME p 
  | A (_, pl) => find_loop2hl pl
and find_loop2hl pl = case pl of
    [] => NONE
  | p :: pm => 
    (case find_loop2h p of SOME r => SOME r | NONE => find_loop2hl pm) 
;

fun fold_one n top = case find_loop2h top of 
    SOME (A ((0,16),[pa,pb,pc,pd,pe])) => 
    let 
      val r = A ((0,13),[pa,pb,mk_add (pc,one),pd,pe])
      val eq1 = mk_eq (r,r) 
      val eq2 = poly ((lhf unfold) eq1)
    in
      funpow n (add_eq_sym eq2) top
    end
  | _ => top;

(* basically linearity of power application *)
fun distrib_pow p = case p of 
  A ((0,9), [A ((0,5), [A ((3,0),[]),px]), pb, A ((0,3),[pc1,pc2])]) => 
  if not (is_num px) then p else 
    A ((0,3),[
      A ((0,9), [A ((0,5), [A ((3,0),[]),px]), pb, pc1]),
      A ((0,9), [A ((0,5), [A ((3,0),[]),px]), pb, pc2])])
  | _ => p;

fun mult_pow p = case p of 
  A ((0,9), [A ((0,5), [A ((3,0),[]),px]), pb, A ((0,5),[pc1,pc2])]) => 
  if not (is_num px) orelse not (is_num pc2) then p else 
    A ((0,5),[A ((0,9), [A ((0,5), [A ((3,0),[]),px]), pb, pc1]), pc2])
  | _ => p;

val (anum,gl) = List.nth (pbl28,0); init_proof gl; 
pgl gl;

val proof15 = induct2_2 >> auto >> refl >> auto >> refl >> 
  ac (lhf unfold) >> ac (lhf unfold) >> ac (lhf (fold_one 2)) >>
  ac (rhf unfold) >> ac (rhf (argf 0 (argf 2 unfold))) >> 
  ac (rhf (argf 0 (argf 2 (argf 1 unfold)))) >> 
  ac (rhf (replace_atl distrib_pow)) >> 
  ac (rhf (argf 1 unfold)) >>  
  ac (replace_atl mult_pow) >> 
  replace_asm 1 >> replace_asm 2 >>
  refl
  
 (((loop (x0 * 2) (1 + x0) (loop2 (x0 + x1) x0 (1 + x0) 1 1)) x0 (loop (x0 * 2) (1 + x0) (loop2 (x0 + x1) x0 x0 1 1))) * 2))   
    
formula_to_poly (snd (hd (hd (!stack))));
  
  
(* todo: make the proof looks like that *)  
u(x+1) = 2*v(x)  

((loop2 (x1 * 2) ((x0 * 2) + (x1 * 2)) x0 1 2)
u(x+2) = 4*(u(x) + v(x))
u(x+2) = 2 * (2*u(x) + u(x+1))
u(x+2) = 4*u(x) + 2*u(x+1)
         
(loop (x0 * 2) x0 (loop2 (x0 + x1) x0 x0 1 1)))
u(x+2) = 2 * 2^(x+1) * (fib (x+1) + fib(x))
u(x+2) = 2 * ((2^(x+1) * fib(x+1)) + (2^(x+1) * fib(x)))
u(x+2) = 2 * u(x+1) + 4*u(x)

(
((loop2 (x1 * 2) ((x0 * 2) + (x1 * 2)) (1 + x0) 1 2) * 2) + 
(((loop2h (x1 * 2) ((x0 * 2) + (x1 * 2)) x0 1 2) * ~4) + 
(
  (
  ((loop2 (x1 * 2) ((x0 * 2) + (x1 * 2)) x0 1 2) * 4) + 
  ((loop2h (x1 * 2) ((x0 * 2) + (x1 * 2)) x0 1 2) * 4)
  )

*)
