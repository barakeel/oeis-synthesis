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
       smtdefspec us 1 (site xs (sapp ts "0") (sapp ts (sincr (sapp us dxs))));
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
 
fun write_anuml file il = 
  writel file (map (fn x => "A" ^ its x ^ ".smt2") (dict_sort Int.compare il))

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
    val lver = ref []
    val lnonver = ref []
    fun test (pp,anuml) = 
      let val (b1,b2) =  verify_eq (1000000,100) pp in
        if (not b1) then b1 else
        if b2 
        then (lver := hd (dict_sort Int.compare anuml) :: !lver; b1)
        else (lnonver := hd (dict_sort Int.compare anuml) :: !lnonver; b1)
      end
    val l5 = filter test l4
    val _ = print_endline ("further verification: " ^ its (length l5))
  in
    mkDir_err dir; clean_dir dir;
    mkDir_err (dir ^ "/pb"); clean_dir (dir ^ "/pb");
    write_anuml (dir ^ "/all_verified100") (!lver);
    write_anuml (dir ^ "/all_nonverified100") (!lnonver);
    app (export_smt2_one flag (dir ^ "/pb")) l5
  end

(* -------------------------------------------------------------------------
   Command to export problems from the files 
   "model/itsol209" to SMTlib (not compatible with z_flag)
   ------------------------------------------------------------------------- *)

(*
load "smt"; open kernel aiLib human smt;
export_smt2 true "oeis-smt" "model/itsol209";
*)

(* -------------------------------------------------------------------------
   Listing problems that likely require induction:
   ------------------------------------------------------------------------- *)

fun all_toploop p = case p of 
    Ins (9,_) => [p]
  | Ins (12,_) => [p]
  | Ins (13,_) => [p]
  | Ins (_,pl) => List.concat (map all_toploop pl)

(* semantic test *)                 
fun both_xy p = depend_on_x p andalso depend_on_y p
fun either_xy p = depend_on_x p andalso depend_on_y p

fun test_syn p = case p of
    Ins (9,[p1,p2,p3]) => (depend_on_x p2) andalso (depend_on_x p1)
  | Ins (12,[p1,p2]) => depend_on_x p2
  | Ins (13,[p1,p2,p3,p4,p5]) => 
    depend_on_x p3 andalso (both_xy p1 orelse both_xy p2)
  | _ => false

(* semantic test *)
fun is_constant_list l = 
  case l of [] => true 
  | [a] => true
  | a :: b :: m => a = b andalso is_constant_list (b :: m)

fun is_almost_constant l = case l of 
    [] => raise ERR "is_almost_constant" ""
  | [a] => raise ERR "is_almost_constant" ""
  | _ => 
  let val r = last l in 
    is_constant_list (butlast l) andalso first_n (length r) (hd l) = r
  end 
  
fun cyclic l = 
  exists is_almost_constant (List.tabulate (15, fn x => mk_batch (x + 1) l))

val xl = 
  List.tabulate (10, fn y => 
    List.tabulate (40, fn x => (IntInf.fromInt x, IntInf.fromInt y)));

val yl = 
  List.tabulate (10, fn x => 
    List.tabulate (40, fn y => (IntInf.fromInt x, IntInf.fromInt y)));

val strict_flag = ref true
val bound_flag = ref false
fun noncyclic_inl p inl =
  let 
    val l = penum2_list p inl 
    val l' = 
      if !bound_flag 
      then List.map (fn x => if IntInf.<= (x,0) then IntInf.fromInt 0 else x) l
      else l
  in
    not (cyclic (snd (part_n 10 l')))
  end
  handle Div => not (!strict_flag)
       | ProgTimeout => not (!strict_flag)
       | Overflow => not (!strict_flag)

fun noncyclic_x p = 
  if not (depend_on_y p) 
  then noncyclic_inl p (hd xl)
  else all (noncyclic_inl p) xl
 
fun noncyclicb_x p =
  let val r = (bound_flag := true; noncyclic_x p) in
    bound_flag := false; r
  end  
  
fun noncyclic_y p = 
  if not (depend_on_x p) 
  then noncyclic_inl p (hd yl)
  else all (noncyclic_inl p) yl  

fun noncyclic_xy p = noncyclic_x p andalso noncyclic_y p 
  
fun test_sem p = 
  noncyclic_x p andalso
  case p of
    Ins (9,[p1,p2,p3]) => (noncyclicb_x p2) andalso (noncyclic_x p1)
  | Ins (12,[p1,p2]) => noncyclicb_x p2
  | Ins (13,[p1,p2,p3,p4,p5]) => 
    noncyclicb_x p3 andalso (noncyclic_xy p1 orelse noncyclic_xy p2)
  | _ => false

fun test_pp test (p1,p2) = 
  let 
    val d = count_dict (dempty prog_compare) (all_toploop p1 @ all_toploop p2)
    val l = filter (fn x => snd x <= 1) (dlist d)
  in
    exists test (map fst l) 
  end
    
fun ind_pb test l = dict_sort Int.compare 
  (map fst (filter (test_pp test o snd) l));

(* -------------------------------------------------------------------------
   Command to create the subbenchmarks
   ------------------------------------------------------------------------- *)

(*
load "smt"; open aiLib kernel smt;

cmd_in_dir "oeis-smt" "ls pb | wc -l > all_pb";
val smt1 = map 
  (fn x => (string_to_int o tl_string) (hd (String.tokens (fn x => x = #".") x))) (readl "oeis-smt/all_pb");
length smt1;
val org = read_itprogl "model/itsol209"; 
length org;
val smt2 = List.mapPartial (fn (x,l) => 
  if length l <> 2 orelse (not (mem x smt1)) 
  then NONE 
  else SOME (x, pair_of_list (dict_sort prog_compare_size (map snd l)))) 
    org;  
length smt2;

val pbsyn = ind_pb test_syn smt2; 
write_anuml "oeis-smt/aind_syn" pbsyn;
val pbsynsem = ind_pb (fn x => test_syn x andalso test_sem x) smt2;
write_anuml "oeis-smt/aind_sem" pbsynsem;
*)


end (* struct *)
