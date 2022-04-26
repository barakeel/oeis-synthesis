structure kernel :> kernel =
struct

open HolKernel Abbrev boolLib aiLib dir;
val ERR = mk_HOL_ERR "kernel";
               
val selfdir = dir.selfdir 

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val maxinput = 128
val overflow = valOf (Int.maxInt)

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)

type exec = int * int -> int
type oper = exec list -> exec

(* -------------------------------------------------------------------------
   Sequences
   ------------------------------------------------------------------------- *)

type seq = int list
val seq_compare = list_compare Int.compare
fun string_of_seq il = String.concatWith " " (map its il)

(* -------------------------------------------------------------------------
   Program
   ------------------------------------------------------------------------- *)

type id = int
datatype prog = Ins of (id * prog list);

fun prog_compare (Ins(s1,pl1),Ins(s2,pl2)) =
  cpl_compare Int.compare (list_compare prog_compare) ((s1,pl1),(s2,pl2))

fun raw_prog (Ins (id,pl)) =
  "(" ^ its id ^ " " ^ String.concatWith " " (map raw_prog pl) ^ ")"

fun equal_prog (a,b) = (prog_compare (a,b) = EQUAL)

fun prog_size (Ins(s,pl)) = case pl of
    [] => 1
  | [a] => 1 + prog_size a
  | [a,b] => 1 + prog_size a + prog_size b
  | _ => (length pl - 1) + sum_int (map prog_size pl) 

fun prog_compare_size (p1,p2) =
  cpl_compare Int.compare prog_compare ((prog_size p1,p1),(prog_size p2,p2))

fun progl_size pl = case pl of
    [] => raise ERR "progl_size" ""
  | _ => (length pl - 1) + sum_int (map prog_size pl)

fun progl_compare_size (pl1,pl2) =
  cpl_compare Int.compare (list_compare prog_compare)  
  ((progl_size pl1,pl1),(progl_size pl2,pl2))

fun all_subprog (p as Ins (_,pl)) = p :: List.concat (map all_subprog pl);

local open HOLsexp in
fun enc_prog (Ins x) = pair_encode (Integer, list_encode enc_prog) x
val enc_progl = list_encode enc_prog
fun dec_prog t = 
  Option.map Ins (pair_decode (int_decode, list_decode dec_prog) t)
val dec_progl = list_decode dec_prog
end

fun write_progl file r = write_data enc_progl file r
fun read_progl file = read_data dec_progl file

(* -------------------------------------------------------------------------
   Instructions
   ------------------------------------------------------------------------- *)

(* id should correspond with index in  operv *)
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
val x_id = 10
val y_id = 11
val compr_id = 12
(* val loop2_id = 13 *)

val ho_ariv = Vector.fromList (List.tabulate (9,fn _ => 0) @ [1,0,0,1,2])

fun depend_on v (Ins (id,pl)) = 
  (id = v) orelse 
  let val hari = Vector.sub (ho_ariv,id) in
    if hari = 0 
    then exists (depend_on v) pl
    else exists (depend_on v) (snd (part_n hari pl))
  end

fun depend_on_x p = depend_on x_id p
fun depend_on_y p = depend_on y_id p

val alpha3 = rpt_fun_type 3 alpha
val alpha4 = rpt_fun_type 4 alpha
val base_operl =
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
   mk_var ("x",alpha),
   mk_var ("y",alpha),
   mk_var ("compr",alpha3)
 (*  ,mk_var ("loop2",rpt_fun_type 6 alpha) *)
  ]
  
val operv = Vector.fromList base_operl
val maxbaseoper = length base_operl
val maxoper = Vector.length operv
val operav = Vector.map arity_of operv
fun arity_of_oper i = arity_of (Vector.sub (operv,i))
fun name_of_oper i = fst (dest_var (Vector.sub (operv,i)))

(* time limit per instruction *)
exception ProgTimeout;
val timelimit = 1000001;
val counter = ref 0;
fun start_counter f x = (counter := 0; f x)
fun test_counter () = (incr counter; 
  if !counter > timelimit then raise ProgTimeout else ())

(* wrappers *)
fun mk_nullf opf fl = case fl of
   [] => (fn x => (test_counter (); opf x))
  | _ => raise ERR "mk_nullf" ""

fun mk_unf opf fl = case fl of
   [f1,f2] => (fn x => (test_counter (); opf (f1 x)))
  | _ => raise ERR "mk_unf" ""

fun mk_binf opf fl = case fl of
   [f1,f2] => (fn x => (test_counter (); opf (f1 x, f2 x)))
  | _ => raise ERR "mk_binf" ""

fun mk_ternf opf fl = case fl of
   [f1,f2,f3] => (fn x => (test_counter (); opf (f1 x, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf" ""

fun mk_binf1 opf fl = case fl of
   [f1,f2] => (fn x => (test_counter (); opf (f1, f2 x)))
  | _ => raise ERR "mk_binf1" ""

fun mk_ternf1 opf fl = case fl of
   [f1,f2,f3] => (fn x => (test_counter (); opf (f1, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf1" ""

fun mk_quintf2 opf fl = case fl of
   [f1,f2,f3,f4,f5] => 
   (fn x => (test_counter (); opf (f1, f2, f3 x, f4 x, f5 x)))
  | _ => raise ERR "mk_quintf2" ""

(* todo change int to Arbint with a maximum limit on the size 
   of arbint *)

(* first-order *)
val zero_f = mk_nullf (fn _ => 0)
val one_f = mk_nullf (fn _ => 1)
val two_f = mk_nullf (fn _ => 2)
val x_f = mk_nullf (fn (x,y) => x)
val y_f = mk_nullf (fn (x,y) => y)
val addi_f = mk_binf (op +)
val diff_f = mk_binf (op -)
val mult_f = mk_binf (op *)
val divi_f = mk_binf (op div)
val modu_f = mk_binf (op mod)
fun cond_f_aux (a,b,c) = if a <= 0 then b else c
val cond_f = mk_ternf cond_f_aux

(* higher-order *)
fun loop_f_aux i f n x = 
  if n <= 0 then x else loop_f_aux (i+1) f (n-1) (f (x,i))
fun loop_f_aux2 (f,n,x) = loop_f_aux 1 f n x
val loop_f = mk_ternf1 loop_f_aux2
fun compr_f_aux x f n0 n =
  if x > (n0+1)*(n0+1)*256 then raise Div
  else if f (x,0) <= 0 then 
   (if n0 >= n then x else compr_f_aux (x+1) f (n0+1) n)
  else compr_f_aux (x+1) f n0 n

fun compr_f_aux2 (f,n) = compr_f_aux 0 f 0 n
val compr_f = mk_binf1 compr_f_aux2
fun loop2_f_aux f1 f2 n x1 x2 = 
  if n <= 0
  then x1 
  else loop2_f_aux f1 f2 (n-1) (f1 (x1,x2)) (f2 (x1,x2))

fun loop2_f_aux2 (f1,f2,n,x1,x2) = loop2_f_aux f1 f2 n x1 x2
val loop2_f = mk_quintf2 loop2_f_aux2

val base_execl =
  [
  zero_f,
  one_f,
  two_f,
  addi_f,
  diff_f,
  mult_f,
  divi_f,
  modu_f,
  cond_f,
  loop_f,
  x_f,
  y_f,
  compr_f
  (*, loop2_f *)
  ]

val base_execv = Vector.fromList base_execl

(* -------------------------------------------------------------------------
   Possible inputs
   ------------------------------------------------------------------------- *)

val entrylx = List.tabulate (maxinput,fn x => (x,0))

fun double_one l = 
  if null l then [] else
  let val (x,y) = last l in
     List.tabulate (x + 1, fn i => (x + i + 1, y))
  end;

fun double_all n x = 
  if n <= 0 then x else
  x @ double_all (n-1) ((map double_one x) @ [[(0,length x)]])

val logmaxinput = 
  Real.round (Math.ln (Real.fromInt maxinput) / Math.ln 2.0);

val entrylxy = List.concat (double_all logmaxinput []);

(* -------------------------------------------------------------------------
   Check the shape of the output.
   ------------------------------------------------------------------------- *)

fun is_constant_aux a m = case m of
    [] => true
  | b :: m => (a:int) = b andalso is_constant_aux b m 

fun is_constant l = if null l then true else is_constant_aux (hd l) (tl l)

fun is_vconstant l0 = 
  let val l1 = filter (not o null) l0 in
    if null l1 then true else
    let
      val l2 = map hd l1
      val l3 = map tl l1
    in    
      is_constant l2 andalso is_vconstant l3
    end
  end;

(* -------------------------------------------------------------------------
   Execute a program on some input
   ------------------------------------------------------------------------- *)

fun mk_exec (Ins (id,pl)) =
  Vector.sub (base_execv,id) (map mk_exec pl)

fun semo_of_prog entryl p =
  let 
    val _ = counter := 0
    val f = mk_exec p
    fun loop l = case l of 
        [] => []
      | a :: m =>
         let val (z,cont) = (f a, fn x => x :: loop m) 
           handle Overflow => (overflow, fn x => [x]) 
                | ProgTimeout => (0, fn x => [])
         in
           cont z
         end  
  in
    SOME (loop entryl) handle Div => NONE
  end   


end (* struct *)
