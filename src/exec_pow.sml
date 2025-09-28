structure exec_pow :> exec_pow =
struct

open HolKernel boolLib aiLib kernel bloom smlParallel
val ERR = mk_HOL_ERR "exec_pow"
type prog = kernel.prog
type exec = IntInf.int -> IntInf.int

(* -------------------------------------------------------------------------
   Time limit
   ------------------------------------------------------------------------- *)

local open IntInf in
  val azero = fromInt 0
  val aone = fromInt 1
  val atwo = fromInt 2
  val aten = fromInt 10  
  fun aincr x = x + aone
  fun adecr x = x - aone
  fun arb_pow a b = if b <= azero then aone else a * arb_pow a (b-aone)
  fun pow2 b = arb_pow atwo (fromInt b)
  val maxarb = arb_pow (fromInt 10) (fromInt maxintsize) (* 4.685 * 10 ^ 284 *)
  val minarb = ~maxarb
  val maxint = fromInt (valOf (Int.maxInt))
  val minint = fromInt (valOf (Int.minInt))
  fun large_arb x = x > maxarb orelse x < minarb
  fun large_int x = x > maxint orelse x < minint
end

fun cost costn x = 
  if large_arb x then raise Overflow else
  if large_int x then IntInf.log2 (IntInf.abs x) else costn

fun checktimer costn y =
  let val _ = abstimer := !abstimer + cost costn y in
    if !abstimer > !timelimit then raise ProgTimeout else y
  end
  
fun cost_pow x = 
  if large_arb x then raise Overflow else 
  if IntInf.abs x < aten then 5 else IntInf.log2 (IntInf.abs x)
  
fun checktimer_pow y =
  let val _ = abstimer := !abstimer + cost_pow y in
    if !abstimer > !timelimit then raise ProgTimeout else y
  end  
  
(* -------------------------------------------------------------------------
   Time limit wrappers
   ------------------------------------------------------------------------- *)

fun mk_nullf opf fl = case fl of
   [] => (fn x => checktimer 1 (opf x))
  | _ => raise ERR "mk_nullf" ""

fun mk_unf opf fl = case fl of
   [f1] => (fn x => checktimer 1 (opf (f1 x)))
  | _ => raise ERR "mk_unf" ""

fun mk_binf costn opf fl = 
  case fl of
   [f1,f2] => (fn x => checktimer costn (opf (f1 x, f2 x)))
  | _ => raise ERR "mk_binf" ""

fun mk_binf_pow opf fl = 
  case fl of
   [f1,f2] => (fn x => checktimer_pow (opf (f1 x, f2 x)))
  | _ => raise ERR "mk_binf_pow" ""

fun cond_f fl = case fl of
   [f1,f2,f3] => 
      (fn x =>
       let 
         val y = if f1 x <= azero then f2 x else f3 x
         val _ = abstimer := !abstimer + 1  
       in
         if !abstimer > !timelimit then raise ProgTimeout else y
       end)
  | _ => raise ERR "mk_condf" ""
  
(* -------------------------------------------------------------------------
   Basic intructions
   ------------------------------------------------------------------------- *)
 
val zero_f = mk_nullf (fn _ => azero)
val one_f = mk_nullf (fn _ => aone)
val two_f = mk_nullf (fn _ => atwo)
val ten_f = mk_nullf (fn _ => aten)
val x_f = mk_nullf (fn x => x)
val addi_f = mk_binf 1 (op +)
val diff_f = mk_binf 1 (op -)
val mult_f = mk_binf 1 (op *)
val divi_f = mk_binf 5 (op div)
val modu_f = mk_binf 5 (op mod)

val maxintsize3 = 3 * maxintsize

fun pow (a,b) = 
  let val b' = IntInf.toInt b in
    if b = azero then aone else
    if a = azero then azero else 
    if IntInf.log2 (IntInf.abs a) * b' > maxintsize3 then raise ProgTimeout
    else IntInf.pow (a,b')
  end

val pow_f = mk_binf_pow pow

(* -------------------------------------------------------------------------
   Execute a program
   ------------------------------------------------------------------------- *)

val execv = Vector.fromList 
  [zero_f,one_f,two_f,addi_f,diff_f,mult_f,divi_f,modu_f,cond_f,pow_f,x_f,ten_f]

fun mk_exec_move id fl = Vector.sub (execv,id) fl
  
fun mk_exec (p as (Ins (id,pl))) = 
  let val fl = map mk_exec pl in mk_exec_move id fl end
  
(*
load "kernel"; open aiLib kernel;
load "bloom"; open bloom;
val ERR = mk_HOL_ERR "test";



fun sappl sl = "(" ^ String.concatWith " " sl ^ ")";
fun sbin opers s1 s2 = sappl [opers,s1,s2];
fun ster opers s1 s2 s3 = sappl [opers,s1,s2,s3];
fun site s1 s2 s3 = ster "ite" (sbin "<=" s1 "0") s2 s3;

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
  | Ins (9,[p1,p2]) => sbin "pow" (smt p1) (smt p2)
  | Ins (10,[]) => "c"
  | Ins (11,[]) => "10"
  | Ins (i,_) => raise ERR "smt" (its i)
;

fun export_smt_one dir ((p1,p2),anumltop) =
  let 
    val _ = if null anumltop then raise ERR "export_smt2_one" "" else ()
    val anuml = dict_sort Int.compare anumltop
    val anums = String.concatWith "-" (map (fn a => "A" ^ its a) anuml)
    val file = dir ^ "/" ^ "A" ^ its (hd anuml) ^ ".smt2" 
    val seq = valOf (Array.sub (bloom.oseq,hd anuml))
    val header =  
      [";; sequence(s): " ^ anums,
       ";; terms: " ^ string_of_seq (first_n 20 seq),
       "(set-logic NIA)"]
    val footer =
       ["(assert (exists ((c Int)) (and (>= c 0) " ^
        "(not (= " ^ smt p1 ^ " " ^ smt p2 ^ ")))))", 
        "(check-sat)"]
  in
    writel file (header @ footer)
  end;

fun export_smt dir file =
  let 
    val sol0 = read_itprogl file;
    val sol1 = filter (fn x => length (snd x) = 2) sol0
    val sol2 = map_snd pair_of_list sol1
    val sol2' = map_snd (fn ((t1,p1),(t2,p2)) => 
       if t1 < t2 then (p2,p1) else (p1,p2)) sol2
    val sol3 = map swap sol2';
    val sol4 = dlist (dregroup (cpl_compare prog_compare prog_compare) sol3);
    val sol5 = filter 
      (fn ((p1,p2),_) => contain_id 9 p1 orelse contain_id 9 p2) sol4;
  in
    mkDir_err dir;
    app (export_smt_one dir) sol5
  end;

export_smt (selfdir ^ "/data_pow_24") "itsol24";
*)



end (* struct *)
