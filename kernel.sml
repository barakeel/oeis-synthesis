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

type seq = Arbint.int list
val seq_compare = list_compare Arbint.compare
fun rm_i s = 
  if String.size s = 0 then s else
  if String.sub (s,String.size s - 1) =  #"i" 
  then String.substring (s,0,String.size s - 1)
  else s;
fun string_of_seq il = String.concatWith " " (map (rm_i o Arbint.toString) il)

(* -------------------------------------------------------------------------
   Program
   ------------------------------------------------------------------------- *)

type id = int
datatype prog = Ins of (id * prog list);

fun prog_compare (Ins(s1,pl1),Ins(s2,pl2)) =
  cpl_compare Int.compare (list_compare prog_compare) ((s1,pl1),(s2,pl2))

(* fun make_assign_big = *)

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
  (if mem id [12,15] then [(hd pl,id)] else []) @ 
  List.concat (map all_subcompr pl)

(* -------------------------------------------------------------------------
   Storing programs
   ------------------------------------------------------------------------- *)

local open HOLsexp in
fun enc_prog (Ins x) = pair_encode (Integer, list_encode enc_prog) x
val enc_progl = list_encode enc_prog
fun dec_prog t = 
  Option.map Ins (pair_decode (int_decode, list_decode dec_prog) t)
val dec_progl = list_decode dec_prog
end

fun write_progl file r = write_data enc_progl file r
fun read_progl file = read_data dec_progl file

local open HOLsexp in
val enc_iprog = pair_encode (Integer, enc_prog)
val enc_iprogl = list_encode enc_iprog
val dec_iprog = pair_decode (int_decode, dec_prog)
val dec_iprogl = list_decode dec_iprog
end

fun write_iprogl file r = write_data enc_iprogl file r
fun read_iprogl file = read_data dec_iprogl file

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
val x_id = 10
val y_id = 11
val compr_id = 12
val loop2_id = 13


val alpha2 = rpt_fun_type 2 alpha
val alpha3 = rpt_fun_type 3 alpha
val alpha4 = rpt_fun_type 4 alpha
val base_operl = [
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
  mk_var ("compr",alpha3),
  mk_var ("loop2",rpt_fun_type 6 alpha),
  mk_var ("condeq", alpha4),
  mk_var ("compreq", alpha3)
  ]

val ratio_operl = [
  mk_var ("numer", alpha2),
  mk_var ("denom", alpha2),
  mk_var ("divr", alpha3),
  mk_var ("intpart", alpha2)
  ]

val mem_operl = [mk_var ("lookup",alpha2), mk_var ("assign",alpha4)]

val operv = Vector.fromList (base_operl @ ratio_operl @ mem_operl)
val maxarity = 5 (* limited by the tnn *)
val operav = Vector.map arity_of operv
fun arity_of_oper i = Vector.sub (operav,i)
fun name_of_oper i = fst (dest_var (Vector.sub (operv,i)))

(* -------------------------------------------------------------------------
   Detect dependencies: ho_ariv should match operv
   ------------------------------------------------------------------------- *)

val ho_ariv = Vector.fromList (List.tabulate (9,fn _ => 0) @ [1,0,0,1,2,0,1]
  @ List.tabulate (length ratio_operl + length mem_operl, fn _ => 0))

fun depend_on v (Ins (id,pl)) = 
  (id = v) orelse 
  let val hari = Vector.sub (ho_ariv,id) in
    if hari = 0 
    then exists (depend_on v) pl
    else exists (depend_on v) (snd (part_n hari pl))
  end

fun depend_on_x p = depend_on x_id p
fun depend_on_y p = depend_on y_id p
fun is_constant p = not (depend_on_x p orelse depend_on_y p)
fun has_compr (Ins (id,pl)) = id = compr_id orelse exists has_compr pl;


(* -------------------------------------------------------------------------
   Timer
   ------------------------------------------------------------------------- *)

exception ProgTimeout;
val rt_glob = ref (Timer.startRealTimer ())
val short_timeincr = 0.00001
val long_timeincr = 0.001
val timeincr = ref short_timeincr
val timelimit = ref (!timeincr)
val small_mem = 100
val big_mem = 10000 
val memsize = ref small_mem

fun incr_timer () = timelimit := !timelimit + !timeincr
val skip_counter = ref 0
fun init_timer () =
  (skip_counter := 0;
   rt_glob := Timer.startRealTimer ();
   timelimit := !timeincr)
   
fun init_fast_test () = (memsize := small_mem; timeincr := short_timeincr)
fun init_slow_test () = (memsize := big_mem; timeincr := long_timeincr)  
 
fun check_timelimit () = 
  let val t = Time.toReal (Timer.checkRealTimer (!rt_glob)) in
    if t > !timelimit then raise ProgTimeout else ()
  end


fun catch_perror f x g =
  f x handle Div => g () 
           | ProgTimeout => g () 
           | Overflow => g ()
   
  
end (* struct *)
