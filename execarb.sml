structure execarb :> execarb =
struct

open HolKernel boolLib aiLib kernel bloom;
val ERR = mk_HOL_ERR "execarb";

val arbentryl = List.tabulate (101,fn x => (Arbint.fromInt x,Arbint.zero))

(* -------------------------------------------------------------------------
   Instructions
   ------------------------------------------------------------------------- *)

val aits = Arbint.toString

fun find_arbmax_aux a m = case m of
    [] => a
  | a1 :: m1 => Arbint.max (a, find_arbmax_aux a1 m1)

fun find_arbmax l = case l of
   [] => raise ERR "find_arbmax" ""
 | a :: m => find_arbmax_aux a m

(* time limit per instruction *)
val arbmaxinput = ref 16
fun timescale () = !arbmaxinput
fun timescale2 () = int_pow (timescale ()) 2
fun timescale4 () = int_pow (timescale ()) 4 + 1

exception ArbOverflow;

local open Arbint in

fun aint_pow (a,b) = if b <= zero then one else a * aint_pow (a, b - one)

val maxarb = (fromInt 5) * aint_pow (fromInt 10, fromInt 284);
val minarb = ~maxarb;

fun protect r = if r > maxarb orelse r < minarb 
  then raise ArbOverflow else r

val arb_zero_f = (fn _ => zero)
val arb_one_f = (fn _ => one)
val arb_two_f = (fn _ => two)
val arb_var_f = (fn (a:Arbint.int,b:Arbint.int) => a)
val arb_ind_f = (fn (a:Arbint.int,b:Arbint.int) => b)

(* first-order *)
fun arb_addi_f (a,b) = protect (a + b)
fun arb_diff_f (a,b) = protect (a - b)
fun arb_mult_f (a,b) = protect (a * b)
fun arb_divi_f (a,b) = protect (a div b)
fun arb_modu_f (a,b) = protect (a mod b)
fun arb_cond_f (a,b,c) = protect (if a <= zero then b else c)

(* higher-order *)
fun arb_loop_f_aux i f n x = 
   (
   incr counter;
   if FixedInt.> (!counter,timescale4 ()) then raise Div
   else if n <= zero then x 
   else arb_loop_f_aux (i+one) f (n-one) (f (x,i))
   )

fun arb_loop_f f (n,x) = arb_loop_f_aux one f n x

fun arb_compr_f_aux x f n0 n =
   (
   if x > (n0+one)*(n0+one)*(Arbint.fromInt (timescale2 ())) then raise Div else ();
   incr counter;
   if FixedInt.> (!counter,timescale4 ()) then raise Div
   else if f (x,zero) <= zero then 
     (if n0 >= n then x else arb_compr_f_aux (x+one) f (n0+one) n)
   else arb_compr_f_aux (x+one) f n0 n
   )

fun arb_compr_f f n = arb_compr_f_aux zero f zero n

end

(* regroup by arity *)
val arb_nullaryl =
 [(zero_id,arb_zero_f),(one_id,arb_one_f),(two_id,arb_two_f),
  (var_id,arb_var_f),(ind_id,arb_ind_f)]

fun find_arb_nullaryf id = assoc id arb_nullaryl
val arb_nullaryv = Vector.tabulate (maxoper, fn i => 
  if can find_nullaryf i then find_arb_nullaryf i else arb_zero_f);

val arb_binaryl = 
  [(addi_id,arb_addi_f),(diff_id,arb_diff_f),(mult_id,arb_mult_f),
   (divi_id,arb_divi_f),(modu_id,arb_modu_f)]
fun find_arb_binaryf id = assoc id arb_binaryl
val arb_binaryv = Vector.tabulate (maxoper, fn i => 
  if can find_binaryf i then find_arb_binaryf i else arb_addi_f);

(* -------------------------------------------------------------------------
   Execute a program on some input
   ------------------------------------------------------------------------- *)

fun compose1 f f1 x = f (f1 x)
fun compose2 f f1 f2 x = f (f1 x, f2 x)
fun compose3 f f1 f2 f3 x = f (f1 x, f2 x, f3 x)

fun arb_mk_exec_aux prog = case prog of
    Ins (id,[]) => Vector.sub (arb_nullaryv,id) 
  | Ins (12,[p1,p2]) =>
    compose1 (arb_compr_f (arb_mk_exec_aux p1)) (arb_mk_exec_aux p2)
  | Ins (id,[p1,p2]) => 
    compose2 (Vector.sub (arb_binaryv,id)) 
       (arb_mk_exec_aux p1) (arb_mk_exec_aux p2)
  | Ins (8,[p1,p2,p3]) => 
    compose3 arb_cond_f (arb_mk_exec_aux p1) 
       (arb_mk_exec_aux p2) (arb_mk_exec_aux p3)
  | Ins (9,[p1,p2,p3]) =>
    compose2 (arb_loop_f (arb_mk_exec_aux p1)) 
       (arb_mk_exec_aux p2) (arb_mk_exec_aux p3)
  | _ => raise ERR "arb_mk_exec_aux" ""  

fun arb_mk_exec p =
  let val exec = start (arb_mk_exec_aux p) in
    (fn x => (exec x handle Div => Arbint.fromInt error 
                          | ArbOverflow => Arbint.fromInt error))
  end 

fun arb_seq_of_prog n p =
  let 
    val _ = arbmaxinput := n
    val f = arb_mk_exec p 
  in 
    map f (first_n n arbentryl) 
  end

val minlength = ref 0
val mininfo = ref 0.0

fun longereq n l =
  if n <= 0 then true else if null l then false else longereq (n-1) (tl l)

val ln2 = Math.ln 2.0;
fun log2 i = Math.ln (Real.abs (Real.fromInt i)) / ln2;
fun info_int i = if i = 0 then 1.0 else log2 i + 1.0;

fun info_arb x = 
   if Arbint.> (x,Arbint.fromInt error) orelse
      Arbint.< (x, Arbint.~ (Arbint.fromInt error))
   then 1.0 else info_int (Arbint.toInt x)
fun info_seq il = sum_real (map info_arb (first_n 16 il))

fun mk_aodnv n =
  let
    val (_,aod) = import_arbseq ()
    val l0 = filter (longereq (!minlength)) (dkeys aod)
    val _ = print_endline (its n ^ " :l0 " ^ its (length l0)) 
    val l1 = filter (fn x => info_seq x > (!mininfo)) l0
    val _ = print_endline (its n ^ " :l1 " ^ its (length l1)) 
    val ln = map (first_n n) l1
    val aodvref = Vector.tabulate (n + 1, 
      fn _ => ref (eempty (list_compare Arbint.compare)))
    fun f seq = 
      let val aodref = Vector.sub (aodvref,length seq) in
        aodref := eadd seq (!aodref)
      end  
    val _ = app f ln
    val r = Vector.map ! aodvref
  in
    r
  end

fun arb_update_wind wind n aodv seq =
  let
    val seql = List.tabulate (n + 1, fn i => 
      let val subseq = first_n i seq in
        if emem subseq (Vector.sub (aodv,i))
        then wind := eadd subseq (!wind)
        else ()
      end)
  in
    ()
  end ;

fun number_seq pl n = 
  let
    val aodnv = mk_aodnv n;
    val wind = ref (eempty (list_compare Arbint.compare));
    val seql = map (arb_seq_of_prog n) pl;
  in
    app (arb_update_wind wind n aodnv) seql;
    elength (!wind)
  end

end (* struct *)

(* Checking Fibonnaci 

fun loop f n l = 
  if n <= 0 then l else loop f (n-1) (f (hd l) :: l);

fun fibonnaci (a,b) = (b, a + b);
val l1 = rev (map fst (loop fibonnaci 20 [(0,1)]));

fun subf x = (x div 4) + 1;
fun iterf x = (((x mod (subf x)) + x) div 2) + x + 1;

val l2 = loop iterf 20 [1];
val l3 = rev (map (fn x => ((x div 2) + 1) div 2) l2);
*)



(* 
load "mcts"; load "execarb";  open aiLib mcts execarb;
PolyML.print_depth 10;
val pl = read_result "sold34";
PolyML.print_depth 40;
length pl;

minlength := 0;
number_seq pl 16;

minlength := 32;
mininfo := 48.0;
val l1 = List.tabulate (17, fn x => number_seq pl (16+x));
val l1freq = map (fn x => int_div x (hd l1)) l1;

minlength := 32;
mininfo := 0.0;
number_seq pl 16;
val l2 = List.tabulate (17, fn x => number_seq pl (16+x));
val l2freq = map (fn x => int_div x (hd l2)) l2;

> 16 :l0 194071
16 :l1 136622
val it = 15122: int
> val it = (): unit
> 16 :l0 194071
16 :l1 194071
val it = 26873: int

val l1 =
   [15122, 13012, 12049, 11325, 10843, 10392, 10106, 9893, 9723, 9537, 9419,
    9321, 9221, 9152, 9112, 9037, 8988]: int list
> val l1freq =
   [1.0, 0.860468192, 0.7967861394, 0.7489088745, 0.7170347838, 0.6872106864,
    0.6682978442, 0.6542124058, 0.6429705065, 0.6306705462, 0.6228673456,
    0.6163867213, 0.6097738394, 0.6052109509, 0.6025657982, 0.5976061368,
    0.5943658246]

val l2 =
   [26873, 20477, 17346, 15525, 14347, 13396, 12862, 12479, 12155, 11803,
    11566, 11417, 11255, 11147, 11079, 10958, 10874]: int list
> val l2freq =
   [1.0, 0.7619915901, 0.6454805939, 0.5777174115, 0.5338815912,
    0.4984929111, 0.4786216649, 0.4643694414, 0.4523127302, 0.439214081,
    0.4303948201, 0.4248502214, 0.4188218658, 0.4148029621, 0.4122725412,
    0.4077698805, 0.4046440665]: real list

val freq = number_fst 16 (combine (l1freq,l2freq));
fun f (a,(b,c)) = its a ^ " " ^ rts b ^ " " ^ rts c;
writel "gendata" (map f freq);
*)


