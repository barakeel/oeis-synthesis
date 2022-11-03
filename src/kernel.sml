structure kernel :> kernel =
struct

open HolKernel Abbrev boolLib aiLib dir;
val ERR = mk_HOL_ERR "kernel";
               
val selfdir = dir.selfdir 

val configd = 
  let 
    val sl = readl (selfdir ^ "/config")
    fun f s = SOME (pair_of_list (String.tokens Char.isSpace s)) 
      handle HOL_ERR _ => NONE
  in
    dnew String.compare (List.mapPartial f sl)
  end

fun bflag s = ref (string_to_bool (dfind s configd) handle NotFound => false)

val z_flag = bflag "z_flag"
val t_flag = bflag "t_flag"
val sol2_flag = bflag "sol2_flag"
val notarget_flag = bflag "notarget_flag"
val prime_flag = bflag "prime_flag"
val hadamard_flag = bflag "hadamard_flag"
val array_flag = bflag "array_flag"
val local_flag = bflag "local_flag"
val sqrt_flag = bflag "sqrt_flag"
val loop_flag = bflag "loop_flag"
val bigvar_flag = bflag "bigvar_flag"

(* -------------------------------------------------------------------------
   Dictionaries shortcuts
   ------------------------------------------------------------------------- *)

type ('a,'b) dict = ('a, 'b) Redblackmap.dict
fun eaddi x d = d := eadd x (!d)
fun ememi x d = emem x (!d)
fun daddi k v d = d := dadd k v (!d) 
fun dmemi x d = dmem x (!d)
fun dfindo k d = SOME (dfind k d) handle NotFound => NONE

(* -------------------------------------------------------------------------
   Sequences
   ------------------------------------------------------------------------- *)

type seq = IntInf.int list
type anum = int
val seq_compare = list_compare IntInf.compare

fun string_of_seq il = String.concatWith " " (map IntInf.toString il)
val amillion = IntInf.fromInt 1000000
fun gpt_of_int i = 
  if i > amillion then "_" 
  else if i < ~amillion then "~_" 
  else IntInf.toString i

fun gpt_of_seq il = String.concatWith " " (map gpt_of_int il)

fun is_prefix seq1 seq2 = case (seq1,seq2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => if a1 = a2 then is_prefix m1 m2 else false

val target_glob = ref []

(* -------------------------------------------------------------------------
   Program
   ------------------------------------------------------------------------- *)

type id = int
datatype prog = Ins of (id * prog list);
type sol = anum * (int * prog) list

fun prog_compare (Ins(s1,pl1),Ins(s2,pl2)) =
  cpl_compare Int.compare (list_compare prog_compare) ((s1,pl1),(s2,pl2))

fun raw_prog (Ins (id,pl)) =
  "(" ^ its id ^ " " ^ String.concatWith " " (map raw_prog pl) ^ ")"

fun equal_prog (a,b) = (prog_compare (a,b) = EQUAL)
fun prog_size (Ins(id,pl)) = 1 + sum_int (map prog_size pl)
fun prog_compare_size (p1,p2) =
  cpl_compare Int.compare prog_compare ((prog_size p1,p1),(prog_size p2,p2))

fun all_subprog (p as Ins (_,pl)) = p :: List.concat (map all_subprog pl)

fun all_subcompr (Ins (id,pl)) =
  (if id = 12 then [hd pl] else []) @ List.concat (map all_subcompr pl)

(* -------------------------------------------------------------------------
   Storing programs
   ------------------------------------------------------------------------- *)

local open HOLsexp in
  fun enc_prog (Ins x) = pair_encode (Integer, list_encode enc_prog) x
  val enc_progl = list_encode enc_prog
  val enc_proglr = pair_encode (enc_progl, enc_real)  
  fun dec_prog t = 
    Option.map Ins (pair_decode (int_decode, list_decode dec_prog) t)
  val dec_progl = list_decode dec_prog
  val dec_proglr = pair_decode (dec_progl, dec_real)
end

fun write_progl file r = write_data enc_progl file r
fun read_progl file = read_data dec_progl file
fun write_proglr file r = write_data enc_proglr file r
fun read_proglr file = read_data dec_proglr file
 
fun write_proglrl file r = write_data (HOLsexp.list_encode enc_proglr) file r
fun read_proglrl file = read_data (HOLsexp.list_decode dec_proglr) file
  
local open HOLsexp in
  val enc_iprog = pair_encode (Integer, enc_prog)
  val enc_iprogl = list_encode enc_iprog
  val dec_iprog = pair_decode (int_decode, dec_prog)
  val dec_iprogl = list_decode dec_iprog
  val enc_itprog = pair_encode (Integer, 
    list_encode (pair_encode (Integer, enc_prog)))
  val enc_itprogl = list_encode enc_itprog
  val dec_itprog = pair_decode (int_decode,
    list_decode (pair_decode (int_decode, dec_prog)))
  val dec_itprogl = list_decode dec_itprog
  val enc_bool = String o bts
  val dec_bool = Option.mapPartial (fn x => SOME (string_to_bool x)) 
                 o string_decode
  val enc_aint = String o IntInf.toString               
  val dec_aint = Option.mapPartial IntInf.fromString 
                 o string_decode              
  val enc_prime = pair_encode (list_encode enc_aint, enc_iprog) 
  val dec_prime = pair_decode (list_decode dec_aint, dec_iprog)
  
end

fun write_iprogl file r = write_data enc_iprogl file r
fun read_iprogl file = read_data dec_iprogl file

fun write_itprogl file r = write_data enc_itprogl file r
fun read_itprogl file = read_data dec_itprogl file

fun write_primel file r = write_data (HOLsexp.list_encode enc_prime) file r
fun read_primel file = read_data (HOLsexp.list_decode dec_prime) file

(* -------------------------------------------------------------------------
   Extra pre-computed instructions
   ------------------------------------------------------------------------- *)

val maxprecomp = if !hadamard_flag andalso !sqrt_flag then 1000 else 10

fun sqrt_aux i (c,a) = 
  if i >= c then 0 else
  if (i * i) mod c = a then i else sqrt_aux (i+1) (c,a)
  
fun sqrt (c,a) = if c <= 0 then 0 else sqrt_aux 0 (c,a)
  
val sqrtv =
  Vector.tabulate (maxprecomp, fn c => Vector.tabulate (c, fn a => sqrt (c,a)))

fun inv_aux i (c,a) = 
  if i >= c then 0 else
  if (i * a) mod c = 1 then i else inv_aux (i+1) (c,a)
  
fun inv (c,a) = if c <= 0 then 0 else inv_aux 0 (c,a)
  
val invv =
  Vector.tabulate (maxprecomp, fn c => Vector.tabulate (c, fn a => inv (c,a)))

fun leastdiv_aux i c =
  if i >= c then c else 
  if c mod i = 0 then i else leastdiv_aux (i+1) c

fun leastdiv a = leastdiv_aux 2 a
  
val leastdivv = 
  Vector.tabulate (maxprecomp, fn x => if x = 0 then 0 else leastdiv x)

(* -------------------------------------------------------------------------
   Instructions
   ------------------------------------------------------------------------- *)

val base_operl = map (fn (x,i) => mk_var (x, rpt_fun_type (i+1) alpha))
  (
  if !hadamard_flag then
    [("zero",0),("one",0),("two",0),
     ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
     ("cond",3),("x",0),("y",0),("z",0)] @
     (if (!bigvar_flag) then [("X",0),("Y",0),("Z",0)] else []) @
     (if (!sqrt_flag) then [("sqrt",2),("inv",2),("leastdiv",1)] else []) @
     (if (!loop_flag) then 
        [("compr",2),("loop",3),("loop2",5),("loop3",7)] else [])
  else if !array_flag then    
    [("zero",0),("one",0),("two",0),
     ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
     ("cond",3),("x",0),("y",0),
     ("array",1),("assign",2),("loop",3)]
  else
    [("zero",0),("one",0),("two",0),
     ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
     ("cond",3),("loop",3),("x",0),("y",0),
     ("compr",2),("loop2",5)] @
     (if (!z_flag) then [("z",0),("loop3",7)] else [])
  )

(* -------------------------------------------------------------------------
   All operators
   ------------------------------------------------------------------------- *)

val operv = Vector.fromList base_operl
val operav = Vector.map arity_of operv
fun arity_of_oper i = Vector.sub (operav,i)
fun name_of_oper i = 
  if i >= Vector.length operv 
  then its i
  else fst (dest_var (Vector.sub (operv,i)))  

(* -------------------------------------------------------------------------
   Detect dependencies: ho_ariv should match operv
   ------------------------------------------------------------------------- *)

fun find_id s = case List.find (fn i => name_of_oper i = s) 
    (List.tabulate (Vector.length operv,I)) of
    SOME id => id
  | NONE => ~1

val x_id = find_id "x"
val y_id = find_id "y"
val z_id = find_id "z"

val ho_ariv = Vector.fromList (
  if !hadamard_flag then 
    if not (!loop_flag) 
    then (List.tabulate (Vector.length operv, fn _ => 0))
    else (List.tabulate (Vector.length operv - 4, fn _ => 0) @ [1,1,2,3]) 
  else if !array_flag
    then (List.tabulate (Vector.length operv - 1, fn _ => 0) @ [1])
  else List.tabulate (9,fn _ => 0) @ [1,0,0,1,2] @
         (if (!z_flag) then [0,3] else [])
  )
  
val _ = if Vector.length ho_ariv <> 
           Vector.length operv
        then raise ERR "ho_ariv" "mismatch with operv"
        else ()
  
fun depend_on v (Ins (id,pl)) = 
  (id = v) orelse 
  let val hari = Vector.sub (ho_ariv,id) in
    if hari = 0 
    then exists (depend_on v) pl
    else exists (depend_on v) (snd (part_n hari pl))
  end

fun depend_on_x p = depend_on x_id p
fun depend_on_y p = depend_on y_id p
fun depend_on_z p = depend_on z_id p
fun is_constant p = 
  not (depend_on_x p orelse depend_on_y p orelse depend_on_z p)

(* -------------------------------------------------------------------------
   Timer
   ------------------------------------------------------------------------- *)

exception ProgTimeout;

val short_timeincr = 1000
val long_timeincr = 100000
val timeincr = ref (if !hadamard_flag then 100000 else short_timeincr)
val timelimit = ref (!timeincr)
val abstimer = ref 0
val short_compr = 40
val long_compr = 200
val max_compr_number = ref (if !hadamard_flag then 27*4 else short_compr)
val graph = ref []
val graphb = ref 0

fun incr_timer () = timelimit := !timelimit + !timeincr
fun init_timer () = (abstimer := 0; timelimit := !timeincr)
fun init_fast_test () = 
  (
  max_compr_number := short_compr; 
  timeincr := short_timeincr
  )
fun init_slow_test () = 
  (
  max_compr_number := long_compr;
  timeincr := long_timeincr
  )

fun catch_perror f x g =
  f x handle Div => g () 
           | ProgTimeout => g () 
           | Overflow => g ()
  
  
(* -------------------------------------------------------------------------
   Gpt interface
   ------------------------------------------------------------------------- *)

(* printer *)
fun gpt_of_id id = Char.toString (Char.chr (65 + id))
  
fun gpt_of_prog (Ins (id,pl)) = 
  String.concatWith " " (map gpt_of_prog pl @ [gpt_of_id id])

(* reader *)
fun id_of_gpt s = 
  let val n = Char.ord (valOf (Char.fromString s)) in n - 65 end

fun movel_of_gpt s = 
  let val sl = String.tokens Char.isSpace s in map id_of_gpt sl end
  
  
  
end (* struct *)
