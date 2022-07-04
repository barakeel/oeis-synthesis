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

fun is_prefix seq1 seq2 = case (seq1,seq2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => if a1 = a2 then is_prefix m1 m2 else false

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
val z_id = 14
val loop3_id = 15

val z_flag = ref true

val base_operl = 
  map (fn (x,i) => mk_var (x, rpt_fun_type (i+1) alpha)) 
  ([("zero",0),("one",0),("two",0),
   ("addi",2),("diff",2),("mult",2),("divi",2),("modu",2),
   ("cond",3),("loop",3),
   ("x",0),("y",0),
   ("compr",2),("loop2",5)] @
  (if (!z_flag) then [("z",0),("loop3",7)] else [])

(* -------------------------------------------------------------------------
   Definition tools
   ------------------------------------------------------------------------- *)

val hole_id = ~1
val hole = Ins (hole_id,[])

fun prog_size_nohole (Ins(s,pl)) = 
  if s = hole_id then 0 else (1 + sum_int (map prog_size_nohole pl))

fun inst_pat_aux (pat as (Ins (id,patl))) instl =  
  if id = hole_id then 
   (case instl of [] => (pat,[]) | a :: m => (a,m))
  else
    let val (argl,newinstl) = inst_patl_aux [] patl instl in
      (Ins (id, argl), newinstl)
    end
and inst_patl_aux argl patl instl = case patl of 
    [] => (rev argl, instl)
  | pata :: patm =>
    let val (arga,newinstl) = inst_pat_aux pata instl in
      inst_patl_aux (arga :: argl) patm newinstl
    end
  
fun inst_pat pat instl = 
  let val (p,newinstl) = inst_pat_aux pat instl in
    if not (null newinstl) then raise ERR "inst_pat" "too many" else p
  end

fun has_hole (Ins (id,pl)) = 
  if id = hole_id then true else exists has_hole pl

fun count_hole (Ins (id,pl)) = 
  if id = hole_id then 1 else sum_int (map count_hole pl)

(* -------------------------------------------------------------------------
   Importing definitions
   ------------------------------------------------------------------------- *)

val def_id = length base_operl

val defl = 
  let val file = selfdir ^ "/def" in
    if exists_file file
    then number_fst def_id (read_progl file) 
    else []
  end

val def_flag = exists_file (selfdir ^ "/def")

val def_operl = 
  map (fn (i,pat) => mk_var ("def" ^ its i,
    rpt_fun_type (count_hole pat + 1) alpha)) defl;

(* -------------------------------------------------------------------------
   All operators
   ------------------------------------------------------------------------- *)

val operv = Vector.fromList (base_operl @ def_operl)
val operav = Vector.map arity_of operv
fun arity_of_oper i = Vector.sub (operav,i)
fun name_of_oper i = fst (dest_var (Vector.sub (operv,i)))  

(* -------------------------------------------------------------------------
   Unfolding definitions
   ------------------------------------------------------------------------- *)

fun mk_def pat =
  if not (has_hole pat) then
  let fun f l = case l of [] => pat | _ => raise ERR "mk_def" "" in
    f
  end
  else inst_pat pat

val defd = dnew Int.compare (map_snd mk_def defl);

fun undef_prog_aux (Ins (id,pl)) = 
  if not (dmem id defd) then Ins (id, map undef_prog_aux pl) else
  let val newp = (dfind id defd) pl in 
    undef_prog_aux newp 
  end

fun undef_prog p = if def_flag then undef_prog_aux p else p

(* -------------------------------------------------------------------------
   Detect dependencies: ho_ariv should match operv
   ------------------------------------------------------------------------- *)

val ho_ariv = Vector.fromList (List.tabulate (9,fn _ => 0) @ [1,0,0,1,2,0,3])

fun depend_on v (Ins (id,pl)) = 
  (id = v) orelse 
  let val hari = Vector.sub (ho_ariv,id) in
    if hari = 0 
    then exists (depend_on v) pl
    else exists (depend_on v) (snd (part_n hari pl))
  end

fun depend_on_x p = depend_on x_id (undef_prog p)
fun depend_on_y p = depend_on y_id (undef_prog p)
fun depend_on_z p = depend_on z_id (undef_prog p)
fun is_constant p = not (depend_on_x p orelse depend_on_y p)

(* -------------------------------------------------------------------------
   Timer
   ------------------------------------------------------------------------- *)

exception ProgTimeout;
val rt_glob = ref (Timer.startRealTimer ())
val short_timeincr = 0.00001
val long_timeincr = 0.01
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
