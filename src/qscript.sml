load "qlang"; load "human"; load "smt_progx"; load "smt_hol";
open aiLib kernel qsyntax qrule qlang sexp;
val ERR = mk_HOL_ERR "test";
val problems = get_problems ();
timelimit := 1000;
 (* time limit per tactic in abstract time *)
init_pb problems;

val stacd = dnew String.compare
  [
  ("decouple1", decouple1),
  ("induct", induct),
  ("auto", auto),
  ("unfold", ac unfold),
  ("asm0", replace_asm 0),
  ("constant_loop2h", ac (replace_bu constant_loop2h))
  ];

init_proofd ();

val stacl1 = ["decouple1", "induct", "auto", "unfold", 
              "constant_loop2h", "asm0"];   
val stacl2 = map_assoc (fn x => dfind x stacd) stacl1;
val policyf = uniform_policy stacl2;

fun second_n n l = snd (part_n n l);
val (_,t) = add_time (app (retry 0.001 policyf o snd)) problems;
dlength (!proofd);
to_disk "qproofs" (dlist (!proofd));

val l = from_disk "qproofs";


val (an,gl) = hd problems; 
debug_flag := true;   
val ro = record stacl2 gl;
debug_flag := false;
dlist (!proofd);


dlength (!proofd);

val r = map_assoc (record stacl2 o snd) problems;
val (pos1,neg1) = partition (isSome o snd) r; changed pos1 69;

init_pb (map fst neg1);
val stacl1 = ["auto"];
val stacl2 = map_assoc (fn x => dfind x stacd) stacl1;
val (an,gl) = hd (map fst neg1); 
debug_flag := true;   
val ro = record stacl2 gl;
debug_flag := false;
val r = map_assoc (record stacl2 o snd) problems;
val (pos2,neg2) = partition (isSome o snd) r; changed pos2 705;


val proof = ac decouple >> inductar >> ac unfold >> replace_asm 0 >> 
  ac (replace_atl constant_loop2h) >> refl;
val (pos2,neg2) = partition (test_pb proof) neg1; changed pos2 43;

val proof = inductar >> ac unfold >> replace_asm 0 >> ac gen_idloop >> 
  drop_asm >> inductar >> ac unfold >> 
  replace_asm 0 >> refl;
val (pos3,neg3) = partition (test_pb proof) neg2; changed pos3 3;

val proof = induct2ar >>
  ac unfold >> ac (lhf unfold) >> apply_asmk 1 (lhf unfold) >>
  addzero_asmk_left 1 >> replace_asm 0 >> ac (rhf (argf 1 unfold)) >> refl;
val (pos4,neg4) = partition (test_pb proof) neg3; changed pos4 17;

val proof = auto >> refl;
val (pos5,neg5) = partition (test_pb proof) neg4; changed pos5 666;

val proof = inductar >> 
  ac unfold >> replace_asm 0 >> ac gen_idloop >> drop_asm >> induct >>
  auto >> refl >> apply_asm simp >> ac unfold >> replace_asm 0 >> refl;
val (pos6,neg6) = partition (test_pb proof) neg5; changed pos6 12;

val proof = inductar >> ac unfold >> ac 
  (lhf unfold) >> replace_asm 0 >> ac (replace_atl constant_loop2h) >> refl;
val (pos7,neg7) = partition (test_pb proof) neg6; changed pos7 3;

val proof = ac simp >> induct2 >> auto >> refl >> ac (eqf eval) >> refl >>
  ac unfold >> ac (rhf (argf 1 unfold)) >> ac (lhf (argf 1 unfold)) >>
  replace_asm 0 >> drop_asm >> ac gen_idloop >> ac (swap_var 1) >> induct >> 
  ac (eqf eval) >> refl >>
  ac (rhf unfold) >> ac (lhf (argf 1 unfold)) >> replace_asm_sym 0 >> 
  drop_asm >> ac gen_idloop >> ac (swap_var 2) >> inductar >>
  ac unfold >> ac (lhf unfold) >> replace_asm 0 >> refl;
val (pos8,neg8) = partition (test_pb proof) neg7; changed pos8 1;

val proof = imitate >> auto >> refl >> auto >> refl >>
  inductar >>
  ac unfold >> ac (replace_atl constant_loop2h) >> replace_asm 0 >> refl;
val (pos9,neg9) = partition (test_pb proof) neg8; changed pos9 1;

val proof  = ac simp >> induct_para >> auto >> refl >> 
  ac unfold >> replace_asm 0 >> replace_asm 1 >> refl >>
  ac unfold >> replace_asm 0 >> replace_asm 1 >> refl;
val (pos10,neg10) = partition (test_pb proof) neg9; changed pos10 10;

val proof = induct2ar >> 
  ac unfold >> ac (lhf (argf 1 (argf 1 unfold))) >> ac (rhf (argf 1 unfold)) 
  >> replace_asm_sym 0 >> replace_asm_sym 1 >> refl;
val (pos11,neg11) = partition (test_pb proof) neg10; changed pos11 15; 

val proof = ac decouple >> inductar >>
  ac unfold >> ac (lhf unfold) >> ac (replace_atl constant_loop2h) >> 
  replace_asm 0 >> refl;
val (pos12,neg12) = partition (test_pb proof) neg11; changed pos12 8;

val proof = repeat (ac (lhf (argf 0 unfold))) >> inductar >>
  ac unfold >> ac (replace_atl constant_loop2h) >> replace_asm 0 >> refl;
val (pos13,neg13) = partition (test_pb proof) neg12; changed pos13 24;

val proof = induct2ar >> 
  ac (lhf unfold) >> ac (lhf unfold) >> ac (lhf (fold_one 2)) >>
  ac (rhf unfold) >> ac (rhf (argf 1 (argf 2 unfold))) >> 
  ac (rhf (argf 0 (argf 2 (argf 1 unfold)))) >> 
  ac (replace_atl pow_mult) >>
  ac (rhf (argf 1 unfold)) >> 
  replace_asm 0 >> replace_asm 1 >>
  ac (replace_atl pow_mult) >> refl
val (pos14,neg14) = partition (test_pb proof) neg13; changed pos14 3;

val proof  = inductar >>
  ac (lhf unfold) >> ac (rhf unfold) >> ac (rhf unfold)
  >> drop_asm >> inductar >> ac unfold >> drop_asm >> cj2 >>
  inductar >> ac unfold >> replace_asm 0 >> refl >> replace_asm 0 
  >> refl;
val (pos15,neg15) = partition (test_pb proof) neg14; changed pos15 5;

val proof = 
  induct2ar >> 
  ac (rhf unfold) >> ac (rhf (argf 1 unfold)) >>
  ac (lhf unfold) >> ac (lhf unfold) >> ac (lhf unfold) >> cj3 >> refl >>
  apply_asmk 0 (lhf unfold) >> addzero_asmk_left 0 >> tl_asm >> 
  replace_asm 1 >> ac simp >> repeat (ac (lhf unfold)) >> replace_asm 0 >> refl
val (pos16,neg16) = partition (test_pb proof) neg15; changed pos16 4;

val proof = ac simp >> ac decouple >> inductar >> 
  ac unfold >>  ac (replace_atl constant_loop2h) >> replace_asm 0 >> refl;  
val (pos17,neg17) = partition (test_pb proof) neg16; changed pos17 37;

val proof = inductar >> ac unfold >> 
  ac (replace_atl linear_loop2h) >> replace_asm 0 >> refl
val (pos18,neg18) = partition (test_pb proof) neg17; changed pos18 24;

val proof = imitate >> refl >> ac decouple >> inductar >>
  ac unfold >> ac (replace_atl constant_loop2h) >> replace_asm 0 >> refl
val (pos19,neg19) = partition (test_pb proof) neg18; changed pos19 6; 

val proof = inductar >> auto >> ac unfold >> replace_asm 0 >> 
  auto >> refl
val (pos20,neg20) = partition (test_pb proof) neg19; changed pos20 1;   

val proof = auto >> inductar >> ac unfold >> 
  ac (replace_atl linear_loop2h) >> replace_asm 0 >> refl 
val (pos21,neg21) = partition (test_pb proof) neg20; changed pos21 31;   

val proof = auto >> ac decouple >> inductar >> 
  repeat (ac unfold) >> ac (replace_atl constant_loop2h) >> replace_asm 0 >>
  refl
val (pos22,neg22) = partition (test_pb proof) neg21; changed pos22 39;    
  
val proof = inductar >> 
  ac unfold >> ac (replace_atl loop2h_to_loop) >> replace_asm 0 >> 
  ac unfold >> refl
val (pos23,neg23) = partition (test_pb proof) neg22; changed pos23 2;

val proof = inductar >> ac unfold >> replace_asm 0 >> ac simp >>
  ac (replace_atl loop2h_to_loop) >>
  ac unfold >> ac (replace_atl pow_mult) >> refl
val (pos24,neg24) = partition (test_pb proof) neg23; changed pos24 4;  

val proof = auto >> ac (replace_atl pow_mult) >> ac decouple_alt >> 
  inductar >> repeat (ac unfold) >> ac (replace_atl constant_loop2h)
  >> replace_asm 0 >> refl
val (pos25,neg25) = partition (test_pb proof) neg24; changed pos25 25;  

val proof = induct2ar >> repeat (ac (lhf unfold)) >> 
  ac (lhf (argf 1 (fold_one 1))) >> ac (rhf unfold) >>
  ac (rhf (argf 1 unfold)) >> 
  ac (rhf (argf 1 (argf 1 (argf 1 (fold_one 1))))) >>
  replace_asm 0 >> replace_asm 1 >> refl
val (pos26,neg26) = partition (test_pb proof) neg25; changed pos26 1;

val proof = induct2ar >> ac unfold >> ac unfoldh >> 
  addzero_asmk_left 0 >> addzero_asmk_left 1 >> refl
val (pos27,neg27) = partition (test_pb proof) neg26; changed pos27 2;  
  
val proof = auto >> inductar >> ac unfold >> addzero_asmk_left 0 >> refl;
val (pos28,neg28) = partition (test_pb proof) neg27; changed pos28 1; 

val proof = ac simp >> inductar >> repeat (ac unfold) >> 
  ac (replace_atl constant_loop2h) >> replace_asm 0 >> refl
val (pos29,neg29) = partition (test_pb proof) neg28; changed pos29 10;

val proof = ac simp >> ac decouple >> inductar >> repeat (ac unfold) >> 
  ac (replace_atl constant_loop2h) >> replace_asm 0 >> refl
val (pos30,neg30) = partition (test_pb proof) neg29; changed pos30 1;

val proof = ac decouple >> inductar >> repeat (ac unfold) >> 
  ac (replace_atl linear_loop2h) >> replace_asm 0 >> refl
val (pos31,neg31) = partition (test_pb proof) neg30; changed pos31 9;

val proof = ac decouple >> inductar >> repeat (ac unfold) >> 
  ac (replace_bu constant_loop2h) >> replace_asm 0 >> 
  ac (replace_atl pow_mult) >> refl
val (pos32,neg32) = partition (test_pb proof) neg31; changed pos32 2;

val proof = ac decouple >> induct2ar >> ac (lhf unfold) >> ac (lhf unfold) >>
  foldlh >> ac (rhf unfold) >> ac unfoldh >> 
  replace_asm 0 >> replace_asm 1 >> refl
val (pos33,neg33) = partition (test_pb proof) neg32; changed pos33 2;

(* idea :  minimize / suggest / search *)
(* maybe create a strategy for eliminate loop2h *)
(* fold_one may only be used under lhf *)


(*
load "qscript";
load "qlang"; open kernel aiLib qlang;

val proof = ac simp >> imitate >> inductar >> ac unfold >> 
  ac (replace_atl constant_loop2h) >> replace_asm 0 >> refl >> refl >> refl;
  
val (pos34,neg34) = partition (test_pb proof) neg33; changed pos34 35;   
  
val test = [hd (shuffle neg34)];  
init_pb test;

((loop2 (x0 + (x0 * x1)) (1 + x1) x0 1 (loop (x0 + (x0 * x1)) x0 1)) = 


(loop2 (x0 * x1) (1 + x1) x0 1 (1 + (loop (x0 * x1) x0 (1 + x0)))))


val proof = ac decouple >> inductar >> ac (lhf unfold) 
 >> ac (replace_atl constant_loop2h) >> ac (rhf unfold) >> ac (replace_atl constant_loop2h) >> replace_asm_sym 0 >> refl;
 
val (pos34,neg34) = partition (test_pb proof) neg33; changed pos34 1; 
 
init_pb neg34; 
((2 * (loop (x0 * x1) (2 * x0) x0)) = 
(2 * ((loop (x0 * x1) x0 2) * (loop2 (x0 * x1) (1 + x1) x0 x0 x0))))
((2 * (loop2 ((4 * x0) + (x0 * x1)) x1 x0 2 x0)) = 
(loop2 (x0 * x1) x1 x0 4 (4 + x0)))




val polf1 = uniformf 
  [
  ("ac unfold", ac unfold),
  ("ac unfoldh", ac unfoldh),
  ("ac (lhf unfold)", ac (lhf unfold)),
  ("foldlh", foldlh),
  ("inductar", inductar), 
  ("induct2ar", induct2ar),
  ("replace_asm 0", replace_asm 0),
  ("replace_asm 1", replace_asm 1),
  ("auto", auto)
  ];

tactic_counter := 0;  
val (r,t) = add_time (map_assoc (searcht polf1 0.01)) problems;
val r' = Real.fromInt (!tactic_counter) / t;
print_endline (rts_round 0 r');

val (posa1,nega1)= partition (isSome o snd) r; 
length posa1;

val (r,t) = add_time (map_assoc (searcht polf1 0.01)) neg33;
val (posa1,nega1)= partition (isSome o snd) r; 
length posa1;

val (a,b) = hd posa1;
val sl = map (fst o fst) (valOf b);
print_endline (String.concatWith " >> apply_all norm_poly >> refl >> " sl);

val proof = ac (lhf unfold) >> auto >> replace_asm 1 >> ac unfoldh >> replace_asm 0 >> replace_asm 1 >> replace_asm 1 >> ac unfold >> replace_asm 0 >> induct2ar >> auto >> ac unfold >> replace_asm 1 >> foldlh >> ac (lhf unfold) >> induct2ar >> auto >> induct2ar >> ac unfoldh >> ac (lhf unfold) >> foldlh >> inductar >> auto >> replace_asm 0 >> auto >> replace_asm 1 >> inductar >> auto >> auto >> inductar >> ac unfold;
val (pos34,neg34) = partition (test_pb proof) neg33; changed pos34 0;

*)
