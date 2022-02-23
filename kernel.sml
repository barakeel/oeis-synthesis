structure kernel :> kernel =
struct

open HolKernel Abbrev boolLib aiLib;
val ERR = mk_HOL_ERR "kernel";

(* change me to the directory where this file is located *)                    
val selfdir = "/home/thibault/oeis-synthesis" 

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val maxinput = ref 16

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)

type oper2 = int * int -> int
type oper3 = int * int * int -> int
type exec = int * int -> int
type seq = int list
val seq_compare = list_compare Int.compare
fun string_of_seq il = String.concatWith " " (map its il)

(* -------------------------------------------------------------------------
   Composing semantics and executables
   ------------------------------------------------------------------------- *)

val error = valOf (Int.maxInt)

(* -------------------------------------------------------------------------
   Program
   ------------------------------------------------------------------------- *)

type id = int
datatype prog = Ins of (id * prog list);

fun prog_compare (Ins(s1,pl1),Ins(s2,pl2)) =
  cpl_compare Int.compare (list_compare prog_compare) ((s1,pl1),(s2,pl2))

fun equal_prog (a,b) = (prog_compare (a,b) = EQUAL)

fun prog_size (Ins(s,pl)) = 
  if null pl
  then 1 + sum_int (map prog_size pl) 
  else sum_int (map prog_size pl) 

fun all_subprog (p as Ins (_,pl)) = p :: List.concat (map all_subprog pl);

(* -------------------------------------------------------------------------
   Instructions
   ------------------------------------------------------------------------- *)

val zero_id = 0
val one_id = 1
val two_id = 2
val addi_id = 3
val diff_id = 4
val mult_id = 5
val divi_id = 6
val modu_id = 7
val cond_id = 8
val loop_id = 9
val var_id = 10
val ind_id = 11
val compr_id = 12

val alpha3 = rpt_fun_type 3 alpha
val alpha4 = rpt_fun_type 4 alpha
val operv = Vector.fromList 
  [
   mk_var ("zero",alpha),
   mk_var ("one",alpha),
   mk_var ("two",alpha),
   mk_var ("addi",alpha3),
   mk_var ("diff",alpha3),
   mk_var ("mult",alpha3),
   mk_var ("divi",alpha3),
   mk_var ("modu",alpha3),
   mk_var ("cond",alpha4),
   mk_var ("loop",alpha4),
   mk_var ("var",alpha),
   mk_var ("ind",alpha),
   mk_var ("compr",alpha3)
  ]

val maxoper = Vector.length operv

val operav = Vector.map arity_of operv

fun name_of_oper i = fst (dest_var (Vector.sub (operv,i)))

(* time limit per instruction *)
val timelimit = ref (16*16*16*16+1);
val counter = ref 0;
fun start f x = (counter := 0; f x)

(* nullary *)
val zero_f = (fn _ => 0)
val one_f = (fn _ => 1)
val two_f = (fn _ => 2)
val var_f = (fn (a:int,b:int) => a)
val ind_f = (fn (a:int,b:int) => b)

(* first-order *)
val addi_f = op +
val diff_f = op -
val mult_f = op *
val divi_f = op div
val modu_f = op mod
fun cond_f (a,b,c) = if a <= 0 then b else c

(* higher-order operator *)
fun loop_f_aux i f n x = 
   (
   incr counter;
   if !counter > !timelimit then raise Div
   else if n <= 0 then x 
   else loop_f_aux (i+1) f (n-1) (f (x,i))
   )

fun loop_f f (n,x) =
  if n > !timelimit then raise Div else loop_f_aux 1 f n x

fun compr_f_aux x f n0 n =
   (
   if x > (n0+1)*(n0+1)*256 then raise Div else ();
   incr counter;
   if !counter > !timelimit then raise Div
   else if f (x,0) <= 0 then 
     (if n0 >= n then x else compr_f_aux (x+1) f (n0+1) n)
   else compr_f_aux (x+1) f n0 n
   )

fun compr_f f n =
  if n > !timelimit orelse n < 0 then raise Div else compr_f_aux 0 f 0 n

(* regroup by arity *)
val nullaryl =
 [(zero_id,zero_f),(one_id,one_f),(two_id,two_f),(var_id,var_f),(ind_id,ind_f)]

val nullaryidl = map fst nullaryl
fun is_nullary id = mem id nullaryidl
fun find_nullaryf id = assoc id nullaryl
val nullaryv = Vector.tabulate (maxoper, fn i => 
  if can find_nullaryf i then find_nullaryf i else zero_f);

val binaryl = 
  [(addi_id,addi_f),(diff_id,diff_f),(mult_id,mult_f),(divi_id,divi_f),
   (modu_id,modu_f)]
val binaryidl = map fst binaryl
fun is_binary id = id >= addi_id andalso id <= modu_id
fun find_binaryf id = assoc id binaryl
val binaryv = Vector.tabulate (maxoper, fn i => 
  if can find_binaryf i then find_binaryf i else addi_f);

fun is_comm id = mem id [addi_id, mult_id]
val binaryidl_nocomm = filter (fn x => not (is_comm x)) binaryidl 

(* -------------------------------------------------------------------------
   Compressed programs
   ------------------------------------------------------------------------- *)

fun depend_on_i p = case p of 
    Ins (id,[]) => id = ind_id 
  | Ins (9,[p1,p2,p3]) => depend_on_i p2 orelse depend_on_i p3
  | Ins (_,pl) => exists depend_on_i pl  

fun under_lambda p = case p of
    Ins (id,[]) => []
  | Ins (9,[p1,p2,p3]) => p1 :: List.concat (map under_lambda [p1,p2,p3])
  | Ins (_,pl) => List.concat (map under_lambda pl)

fun has_lambdai p = case p of
    Ins (id,[]) => false
  | Ins (9,[p1,p2,p3]) => depend_on_i p1 
     orelse has_lambdai p2 orelse has_lambdai p3
  | Ins (_,pl) => exists has_lambdai pl

(* -------------------------------------------------------------------------
   Compressed programs
   ------------------------------------------------------------------------- *)

type progi = Arbint.int

val progi_compare = Arbint.compare
fun equal_progi (a,b) = (progi_compare (a,b) = EQUAL)

fun suc x = x + 1
fun pred x = x - 1

local open Arbint in

val arbmaxoper = fromInt (suc maxoper)

fun zip_prog prog =
  let
    fun polish (Ins (id,pl)) = fromInt (suc id) :: List.concat (map polish pl)
    fun loop r il = case il of 
        [] => r 
      | a :: m => loop (r * arbmaxoper + a) m 
  in
    loop zero (rev (polish prog))
  end

fun unzip_progl arbi =
  let 
    val (q,r) = Arbint.divmod (arbi, arbmaxoper)
    val id = pred (toInt r)
    val a = Vector.sub (operav,id)
    val pl = if q = zero then [] else unzip_progl q
    val (pla,plb) = part_n a pl
  in
    Ins (id,pla) :: plb
  end

fun unzip_prog arbi = singleton_of_list (unzip_progl arbi)

val hseq_modw = fromInt 2115908027

fun pi_to_hseq pi =
  let val (q,r) = Arbint.divmod (pi, hseq_modw) in
    if q = zero 
    then [toInt r]
    else toInt r :: pi_to_hseq q
  end

end (* local *)

(* -------------------------------------------------------------------------
   Possible inputs
   ------------------------------------------------------------------------- *)

val entryl = List.concat [
  List.tabulate (16,fn x => (x,0)),
  List.tabulate (8,fn x => (x,1)),
  List.tabulate (4,fn x => (x,2)),
  List.tabulate (2,fn x => (x,3)),
  List.tabulate (1,fn x => (x,4))
  ];

val entryl16 = first_n 16 entryl

(* -------------------------------------------------------------------------
   Execute a program on some input
   ------------------------------------------------------------------------- *)

fun compose1 f f1 x = f (f1 x)
fun compose2 f f1 f2 x = f (f1 x, f2 x)
fun compose3 f f1 f2 f3 x = f (f1 x, f2 x, f3 x)

fun mk_exec_aux prog = case prog of
    Ins (id,[]) => Vector.sub (nullaryv,id) 
  | Ins (12,[p1,p2]) =>
    compose1 (compr_f (mk_exec_aux p1)) (mk_exec_aux p2)
  | Ins (id,[p1,p2]) => 
    compose2 (Vector.sub (binaryv,id)) (mk_exec_aux p1) (mk_exec_aux p2)
  | Ins (8,[p1,p2,p3]) => 
    compose3 cond_f (mk_exec_aux p1) (mk_exec_aux p2) (mk_exec_aux p3)
  | Ins (9,[p1,p2,p3]) =>
    compose2 (loop_f (mk_exec_aux p1)) (mk_exec_aux p2) (mk_exec_aux p3)
  | _ => raise ERR "mk_exec" ""  

fun mk_exec p =
  let val exec = start (mk_exec_aux p) in
    (fn x => ((exec x,!counter) handle Overflow => (error,!counter)))
  end 

fun not_semdep_on_i e31 =
  let
    val (e16,e15) = part_n 16 e31
    val (e8,e7) = part_n 8 e15
    val (e4,e3) = part_n 4 e7
    val (e2,e1) = part_n 2 e3
  in
    seq_compare (first_n 8 e16, e8) = EQUAL andalso
    seq_compare (first_n 4 e16, e4) = EQUAL andalso
    seq_compare (first_n 2 e16, e2) = EQUAL andalso
    seq_compare (first_n 1 e16, e1) = EQUAL
  end

fun semtimo_of_prog p =
  let val f = mk_exec p in
    if not (depend_on_i p) 
    then 
      let 
        val e16 = map f entryl16
        val r = 
          (e16 @ first_n 8 e16 @ first_n 4 e16 @ first_n 2 e16 @ first_n 1 e16)
        val (sem,timl) = split r
        val tim = 31 + sum_int timl
      in
        SOME (sem,tim)
      end
      handle Div => NONE
    else
      let 
        val r = map f entryl 
        val (sem,timl) = split r
        val tim = 31 + sum_int timl
      in
        if not_semdep_on_i sem then NONE else SOME (sem,tim)
      end
      handle Div => NONE
  end

fun semo_of_prog p = Option.map fst (semtimo_of_prog p)

fun same_sem p1 p2 = case (semo_of_prog p1, semo_of_prog p2) of
     (SOME l1, SOME l2) => seq_compare (l1,l2) = EQUAL
   | _ => false

val sem_of_prog = valOf o semo_of_prog

fun seq_of_prog p = first_n 16 (sem_of_prog p)

fun is_executable x = isSome (semo_of_prog x)

(* -------------------------------------------------------------------------
   Applications of an instruction syntactically from compressed programs
   ------------------------------------------------------------------------- *)

fun papp_nullop id = Ins (id,[])
fun papp_binop id (p1,p2) = Ins (id, [p1,p2])
fun papp_ternop id (p1,p2,p3) = Ins (id,[p1,p2,p3])

(* -------------------------------------------------------------------------
   Human readable output
   ------------------------------------------------------------------------- *)

val constnorm_flag = ref false
val polynorm_flag = ref true

fun constnorm prog = case prog of
    Ins (0,[]) => 0
  | Ins (1,[]) => 1
  | Ins (2,[]) => 2
  | Ins (3,[p1,p2]) => addi_f (constnorm p1,constnorm p2)
  | Ins (4,[p1,p2]) => diff_f (constnorm p1,constnorm p2)
  | Ins (5,[p1,p2]) => mult_f (constnorm p1,constnorm p2)
  | Ins (6,[p1,p2]) => divi_f (constnorm p1,constnorm p2)
  | Ins (7,[p1,p2]) => modu_f (constnorm p1,constnorm p2)
  | _ => raise ERR "constnorm" ""

fun polyaddi l1 l2 = case (l1,l2) of
    (l1,[]) => l1
  | ([],l2) => l2
  | (a1 :: m1, a2 :: m2) => addi_f (a1,a2) :: polyaddi m1 m2

fun polydiff l1 l2 = case (l1,l2) of
    (l1,[]) => l1
  | ([],l2) => polydiff (List.tabulate (length l2, fn _ => 0)) l2
  | (a1 :: m1, a2 :: m2) => diff_f (a1,a2) :: polydiff m1 m2

fun polymult l1 l2 = case (l1,l2) of 
    (l1,[]) => raise ERR "polymult" ""
  | ([],l2) => raise ERR "polymult" ""
  | (l1,[a]) => map (fn x => mult_f (a,x)) l1
  | ([a],l2) => map (fn x => mult_f (a,x)) l2
  | (a1 :: m1, l2) => 
    polyaddi (map (fn x => mult_f (a1,x)) l2)  (polymult m1 (0 :: l2))

fun polydivi l1 l2 = case (l1,l2) of
    ([a],[b]) => [divi_f (a,b)]
  | _ => raise ERR "polydivi" ""
fun polymodu l1 l2 = case (l1,l2) of
    ([a],[b]) => [modu_f (a,b)]
  | _ => raise ERR "polymodu" ""

fun polynorm prog = case prog of
    Ins (0,[]) => [0]
  | Ins (1,[]) => [1]
  | Ins (2,[]) => [2]
  | Ins (3,[p1,p2]) => polyaddi (polynorm p1) (polynorm p2)
  | Ins (4,[p1,p2]) => polydiff (polynorm p1) (polynorm p2)
  | Ins (5,[p1,p2]) => polymult (polynorm p1) (polynorm p2)
  | Ins (6,[p1,p2]) => polydivi (polynorm p1) (polynorm p2)
  | Ins (7,[p1,p2]) => polymodu (polynorm p1) (polynorm p2)
  | Ins (10,[]) => [0,1]
  | _ => raise ERR "polynorm" ""

fun string_of_mono (a,i) = 
  (if a = 1 andalso i <> 0 then "" else 
   if a = ~1 andalso i <> 0 then "~" else its a) ^ 
  (if i = 0 then "" else if i = 1 then "x" else "x" ^ its i)

fun string_of_poly l = 
  let val l1 = filter (fn x => fst x <> 0) (number_snd 0 l) in
    if null l1 then "0" else
    let val s = String.concatWith " + " (map string_of_mono (rev l1)) in
      if length l1 = 1 then s else "(" ^ s ^ ")"
    end
  end

fun polyaddil l = case l of 
    [] => [] 
  | a :: m => polyaddi a (polyaddil m)

fun polymultl l = case l of 
    [] => raise ERR "polymultl" ""
  | [a] => a 
  | a :: m => polymult a (polymultl m)

fun rm_par s = 
  if String.size s = 0 then s else
  if String.sub (s,0) = #"(" andalso String.sub (s,String.size s - 1) =  #")" 
  then String.substring (s,1,String.size s - 2)
  else s;

(* regroup polynoms in repeated addition/substraction and
   multiplications *)

fun strip_addi p = case p of
    Ins (3,[p1,p2]) => 
    let 
      val (a1,b1) = strip_addi p1 
      val (a2,b2) = strip_addi p2
    in
      (a1 @ a2, b1 @ b2)
    end 
  | Ins (4,[p1,p2]) =>
    let 
      val (a1,b1) = strip_addi p1
      val (a2,b2) = strip_addi p2
    in
      (a1 @ b2, a2 @ b1)
    end 
  | _ => ([p],[])

fun strip_mult p = case p of
    Ins (5,[p1,p2]) => strip_mult p1 @ strip_mult p2 
  | _ => [p]

fun human prog = 
  if !constnorm_flag andalso can constnorm prog then its (constnorm prog) else
  case prog of
    Ins (3,[p1,p2]) => 
    if !polynorm_flag then reg_add prog
    else "(" ^ human p1 ^ " + " ^ human p2 ^ ")"   
  | Ins (4,[p1,p2]) =>  
    if !polynorm_flag then reg_add prog
    else "(" ^ human p1 ^ " - " ^ human p2 ^ ")"   
  | Ins (5,[p1,p2]) =>
    if !polynorm_flag then reg_mult prog
    else "(" ^ human p1 ^ " * " ^ human p2 ^ ")"
  | Ins (6,[p1,p2]) => "(" ^ human p1 ^ " div " ^ human p2 ^ ")"
  | Ins (7,[p1,p2]) => "(" ^ human p1 ^ " mod " ^ human p2 ^ ")"
  | Ins (8,[p1,p2,p3]) => 
     "(if " ^  human p1 ^ " <= 0 then " ^ human p2 ^ " else " ^ human p3 ^ ")"
  | Ins (9,[p1,p2,p3]) => 
    "loop(\\(x,i)." ^ human p1 ^ "," ^ human p2 ^ "," ^ human p3 ^ ")"
  | Ins (10,[]) => "x"
  | Ins (11,[]) => "i"
  | Ins (12,[p1,p2]) => 
    "compr(\\x." ^ human p1 ^ "," ^ human p2 ^ ")" 
  | Ins (s,[]) => its s
  | Ins (s,l) => "(" ^ its s ^ " " ^ String.concatWith " " (map human l) ^ ")"

and reg_add p = 
  let 
    val (pl1,pl2) = strip_addi p
    val (pl1a,pl1b) = partition (can polynorm) pl1
    val (pl2a,pl2b) = partition (can polynorm) pl2
    val pl1n = map polynorm pl1a
    val pl2n = map polynorm pl2a
    fun human_addl pl = case pl of 
         [] => raise ERR "reg_add" ""
       | [a] => human a 
       | _ => "(" ^ String.concatWith " + " (map human pl) ^ ")"
    val polyo = if null pl1n andalso null pl2n then NONE else 
      SOME (polydiff (polyaddil pl1n) (polyaddil pl2n)) 
  in
    case (polyo,pl1b,pl2b) of
      (NONE,[],[]) => raise ERR "reg_add 2" ""
    | (NONE,_,[]) => human_addl pl1b
    | (NONE,[],_) => "~" ^ human_addl pl2b
    | (NONE,_,_) => "(" ^ human_addl pl1b ^ " - " ^ human_addl pl2b ^ ")"
    | (SOME poly,[],[]) => string_of_poly poly 
    | (SOME poly,_,[]) => "(" ^ string_of_poly poly ^ 
      " + " ^ human_addl pl1b ^ ")"
    | (SOME poly,[],_) => "(" ^ string_of_poly poly ^ 
      " - " ^ human_addl pl2b ^ ")"
    | (SOME poly,_,_) => "(" ^ string_of_poly poly ^ 
      " + " ^ human_addl pl1b ^ " - " ^ human_addl pl2b ^ ")"
  end

and reg_mult p =
  let 
    val pl = strip_mult p 
    val (pla,plb) = partition (can polynorm) pl
    fun human_multl pl = case pl of 
         [] => raise ERR "reg_mult" ""
       | [a] => human a 
       | _ => "(" ^ String.concatWith " * " (map human pl) ^ ")"
    val polyo = if null pla then NONE else 
      SOME (polymultl (map polynorm pla))  
  in
    case (polyo,plb) of 
      (NONE,[]) => raise ERR "reg_mult 2" ""
    | (NONE,_) => human_multl plb
    | (SOME poly,[]) => string_of_poly poly
    | (SOME poly,_) => "(" ^ string_of_poly poly ^ " * " ^ 
      human_multl plb ^ ")"
  end

(* -------------------------------------------------------------------------
   Timer
   ------------------------------------------------------------------------- *)

val search_time = ref (Time.fromReal 60.0)
val search_steps = ref (valOf (Int.maxInt))
val rt_glob = ref (Timer.startRealTimer ())
val rti_glob = ref 0

exception SearchTimeout;

fun init_timer () = 
  (rti_glob := 0; rt_glob := Timer.startRealTimer ())

fun check_timer () = 
  (
  if !rti_glob mod 100000 = 0 then print "." else ();
  if !rti_glob > !search_steps orelse
     (!rti_glob mod 100 = 0 andalso 
      Timer.checkRealTimer (!rt_glob) > !search_time)
  then raise SearchTimeout 
  else incr rti_glob
  )

end (* struct *)





