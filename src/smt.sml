structure smt :> smt =
struct

open HolKernel Abbrev boolLib aiLib dir kernel human exec
val ERR = mk_HOL_ERR "smt"


(* -------------------------------------------------------------------------
   Export to SMTlib (not compatible with z_flag)
   ------------------------------------------------------------------------- *)

val defl = ref []
val decl = ref []
val index = ref 0

fun nvar p = 
  if depend_on_z p then 3 else 
  if depend_on_y p then 2 else
  if depend_on_x p then 1 else 0

val varl = ["x","y","z"]

val xs = "x"
val ys = "y"
val zs = "z"  
fun sappl sl = "(" ^ String.concatWith " " sl ^ ")"
fun natapp s n = if n <= 0 then s else sappl (s :: first_n n varl)
fun natarg s n sl = if n <= 0 then s else sappl (s :: first_n n sl)
fun ster opers s1 s2 s3 = sappl [opers,s1,s2,s3]
fun sbin opers s1 s2 = sappl [opers,s1,s2]
fun sapp opers s1 = sappl [opers,s1] 
fun sassert s = sapp "assert" s
fun svar vs = sapp vs "Int"
fun svarl vsl = sappl (map svar vsl)
fun sall vsl body = sbin "forall" (svarl vsl) body
fun site s1 s2 s3 = ster "ite" (sbin "<=" s1 "0") s2 s3
fun sequ s1 s2 = sbin "=" s1 s2
fun sdecr s1 = sbin "-" s1 "1"
fun sincr s1 = sbin "+" s1 "1"
val dxs = sdecr xs
val ixs = sincr xs

fun nint n = sappl (List.tabulate (n,fn _ => "Int"))
fun declaref (s,n) = ster "declare-fun" s (nint n) "Int" 
 
fun smt prog = case prog of
    Ins (0,[]) => "0" 
  | Ins (1,[]) => "1" 
  | Ins (2,[]) => "2" 
  | Ins (3,[p1,p2]) => sbin "+" (smt p1) (smt p2)
  | Ins (4,[p1,p2]) => sbin "-" (smt p1) (smt p2)
  | Ins (5,[p1,p2]) => sbin "*" (smt p1) (smt p2)
  | Ins (6,[p1,p2]) => sbin "div" (smt p1) (smt p2)
  | Ins (7,[p1,p2]) => sbin "mod" (smt p1) (smt p2)
  | Ins (8,[p1,p2,p3]) => site (smt p1) (smt p2) (smt p3)
  | Ins (9,[p1,p2,p3]) =>
    let 
      val (n0,n1,n2,n3) = (nvar prog, nvar p1, nvar p2, nvar p3)
      val (fs,gs,hs,us,vs) = quintuple_of_list 
        (map (fn x => x ^ its (!index)) ["f","g","h","u","v"])  
      val _ = incr index
      val _ = app smtdef [(fs,p1),(gs,p2),(hs,p3)]
     in
       smtdefspec us 2 (site xs ys 
         (natarg fs n1 [(sbin us dxs ys), xs]));
       smtdefspec vs n0 (sbin us (natapp gs n2) (natapp hs n3));
       natapp vs n0
     end
  | Ins (10,[]) => xs
  | Ins (11,[]) => ys
  | Ins (12,[p1,p2]) => 
    let 
      val (n0,n1,n2) = (nvar prog, nvar p1, nvar p2)
      val (fs,gs,ts,us,vs) = quintuple_of_list 
        (map (fn x => x ^ its (!index)) ["f","g","t","u","v"])  
      val _ = incr index
      val _ = app smtdef [(fs,p1),(gs,p2)]
     in
       smtdefspec ts 1 (site (natarg fs n1 [xs,"0"]) xs (sapp ts ixs));
       smtdefspec us 1 (site xs (sapp ts "0") (sapp ts (sapp us dxs)));
       smtdefspec vs n0 (sapp us (natapp gs n2));
       natapp vs n0
     end
  | Ins (13,[p1,p2,p3,p4,p5]) => 
    let 
      val (n0,n1,n2,n3,n4,n5) = 
        (nvar prog, nvar p1, nvar p2, nvar p3, nvar p4, nvar p5)
      val (fs,gs,hs,is,js) = quintuple_of_list 
        (map (fn x => x ^ its (!index)) ["f","g","h","i","j"])
      val (us,vs,ws) = triple_of_list 
        (map (fn x => x ^ its (!index)) ["u","v","w"])
      val _ = incr index
      val _ = app smtdef [(fs,p1),(gs,p2),(hs,p3),(is,p4),(js,p5)]
    in
      smtdefspec us 3 (site xs ys 
        (natarg fs n1 [ster us dxs ys zs,ster vs dxs ys zs]));
      smtdefspec vs 3 (site xs zs 
        (natarg gs n2 [ster us dxs ys zs,ster vs dxs ys zs]));
      smtdefspec ws n0 (ster us (natapp hs n3) (natapp is n4) (natapp js n5));
      natapp ws n0
    end
  | _ => raise ERR "smt" (humanf prog)

and smtdefspec s n r = 
  let val vl = first_n n varl in  
    decl := !decl @ map declaref [(s,n)];
    defl := !defl @ map sassert
      [if n <= 0 then sequ s r else sall vl (sequ (sappl (s :: vl)) r)]
  end
  
and smtdef (s,p) = smtdefspec s (nvar p) (smt p)

fun export_smt2_one flag dir ((p1,p2),anumltop) =
  let 
    val _ = if null anumltop then raise ERR "export_smt2_one" "" else ()
    val anuml = dict_sort Int.compare anumltop
    val anums = String.concatWith "-" (map (fn a => "A" ^ its a) anuml)
    val file = dir ^ "/" ^ "A" ^ its (hd anuml) ^ ".smt2" 
    val seq = valOf (Array.sub (bloom.oseq,hd anuml))
    val _ = (index := 0; decl := []; defl := [])
    val _ = (smtdef ("small",p1), smtdef ("fast",p2))
    val header =  
      [";; sequence(s): " ^ anums,
       ";; terms: " ^ string_of_seq (first_n 20 seq),
       ";; small program: " ^ humanf p1,
       ";; fast program: " ^ humanf p2,
       "(set-logic UFNIA)"]
    val footer =
      (if flag then 
       ["(assert (exists ((c Int)) (and (>= c 0) " ^ 
        "(not (= (small c) (fast c))))))"] else []) @
      ["(check-sat)"]
  in
    writel file (header @ !decl @ !defl @ footer)
  end
  
fun export_smt2 flag dir file =
  let
    val l1 = read_itprogl file
    val _ = print_endline ("sequences: " ^ its (length l1))
    val l2 = List.mapPartial (fn (x,l) => 
      if length l <> 2 then NONE else SOME (x, pair_of_list 
      (dict_sort prog_compare_size (map snd l)))) l1
    val _ = print_endline ("with at least 2 programs: " ^ its (length l2))
    val l3 = map swap l2
    val l4 = dlist (dregroup (cpl_compare prog_compare prog_compare) l3)
    val _ = print_endline ("unique program pairs: " ^ its (length l4))
    val l5 = filter (fn (pp,_) => verify_eq (1000000,100) pp) l4
    val _ = print_endline ("further verification: " ^ its (length l5))
  in
    clean_dir dir;
    app (export_smt2_one flag dir) l5
  end


(*
load "smt"; open kernel aiLib human smt;
export_smt2 true "oeis-smt/pb" "model/itsol209";
*)



end (* struct *)
