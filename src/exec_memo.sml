structure exec_memo :> exec_memo =
struct

open HolKernel boolLib aiLib kernel bloom
val ERR = mk_HOL_ERR "exec_memo"
type prog = kernel.prog
type exec = IntInf.int list * IntInf.int list -> IntInf.int list


(* load "kernel"; open kernel aiLib; *)

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

(* arcagi *)
val mati_glob = ref (Array2.tabulate Array2.RowMajor (1,1,fn (a,b) => 0))
val dimi_glob = ref (IntInf.fromInt 1,IntInf.fromInt 1)
val dimo_glob = ref (IntInf.fromInt 1,IntInf.fromInt 1)
val coliv_glob = ref (Vector.fromList [0])
(* ramsey *)
val n_glob = ref (IntInf.fromInt 0)

(* -------------------------------------------------------------------------
   Mark constant programs with true
   ------------------------------------------------------------------------- *)

datatype progb = Insb of (id * bool * progb list);

fun is_const (Insb (_,b,_)) = b

fun mk_progb (Ins (id,pl)) = 
  if null pl then 
    if id = x_id orelse id = y_id 
    then (Insb (id,false,[])) 
    else (Insb (id,true,[]))
  else
  let 
    val newpl = map mk_progb pl
    val hari = Vector.sub (ho_ariv,id) 
  in
    if hari = 0 
    then Insb (id, all is_const newpl, newpl)
    else Insb (id, all is_const (snd (part_n hari newpl)), newpl)
  end

(* -------------------------------------------------------------------------
   A local memory for each loop (memoization)
   ------------------------------------------------------------------------- *)

val empty_infl = []: IntInf.int list
val default_entry = (empty_infl, empty_infl)

fun get_mem () = ref (Array.array (16, default_entry))

fun resize_array a n = 
  let val dest = Array.array (2 * n, default_entry) in
    Array.copy {src = !a, dst = dest, di = 0};
    a := dest
  end

fun store_mem ((mema,memn),n,x) = 
  if n >= memo_number then () else
  let val meman = Array.length (!mema) in
    if n >= meman then resize_array mema meman else ();
    Array.update (!mema,n,x); 
    memn := n + 1
  end

(* -------------------------------------------------------------------------
   Time limit wrappers
   ------------------------------------------------------------------------- *)  
  
local open IntInf in
  val aonem = fromInt (~1)
  val azero = fromInt 0
  val aone = fromInt 1
  val atwo = fromInt 2
  fun aincr x = x + aone
  fun adecr x = x - aone
  val maxint = fromInt (valOf (Int.maxInt))
  val minint = fromInt (valOf (Int.minInt))
  fun large_int x = x > maxint orelse x < minint
  fun arb_pow a b = if b <= azero then aone else a * arb_pow a (b-aone)
  fun pow2 b = arb_pow atwo (fromInt b)
  val maxarb = arb_pow (fromInt 10) (fromInt maxintsize)
  val minarb = ~maxarb
  val large_arb = 
    if !maxint_flag 
    then (fn x => x > maxarb orelse x < minarb)
    else (fn x => false)
end

fun checktimer y = 
  (
  incr abstimer; 
  if !abstimer > !timelimit then raise ProgTimeout else y
  )

fun mylog x = if x = 0 then 1 else IntInf.log2 x
  
fun costadd costn x1 x2 y =
  if large_int x1 orelse large_int x2 orelse large_int y then 
    if large_arb y then raise ProgTimeout else
    Int.max (mylog (IntInf.abs x1), mylog (IntInf.abs x2))
  else costn
  
fun costmult costn x1 x2 y =
  if large_int x1 orelse large_int x2 orelse large_int y then 
    if large_arb y then raise ProgTimeout else
    mylog (IntInf.abs x1) + mylog (IntInf.abs x2)
  else costn

fun checktimeradd costn x1 x2 y =
  (
  abstimer := !abstimer + costadd costn (hd x1) (hd x2) (hd y);
  if !abstimer > !timelimit then raise ProgTimeout else y
  )

fun checktimermult costn x1 x2 y =
  (
  abstimer := !abstimer + costmult costn (hd x1) (hd x2) (hd y);
  if !abstimer > !timelimit then raise ProgTimeout else y
  )

(* -------------------------------------------------------------------------
   Time limit wrappers
   ------------------------------------------------------------------------- *)

fun mk_nullf opf fl = case fl of
   [] => (fn x => checktimer (opf x))
  | _ => raise ERR "mk_nullf" ""

fun mk_unf opf fl = case fl of
   [f1] => (fn x => checktimer (opf (f1 x)))
  | _ => raise ERR "mk_unf" ""

fun mk_binfadd costn opf fl = case fl of
   [f1,f2] => (fn x => 
     let 
       val (x1,x2) = (f1 x,f2 x) 
       val y  = opf (x1,x2)
     in
       checktimeradd costn x1 x2 y
     end)
  | _ => raise ERR "mk_binfadd" ""

fun mk_binfmult costn opf fl = case fl of
   [f1,f2] => (fn x => 
     let 
       val (x1,x2) = (f1 x,f2 x) 
       val y  = opf (x1,x2)
     in
       checktimermult costn x1 x2 y
     end)
  | _ => raise ERR "mk_binfmult" ""

fun mk_binf opf fl = case fl of
   [f1,f2] => (fn x => checktimer (opf (f1 x, f2 x)))
  | _ => raise ERR "mk_binf" ""

fun mk_ternf opf fl = case fl of
   [f1,f2,f3] => (fn x => checktimer (opf (f1 x, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf" ""

fun mk_ternf1 opf fl = case fl of
   [f1,f2,f3] => (fn x => checktimer (opf (f1, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf1" ""

fun mk_quadf opf fl = case fl of
   [f1,f2,f3,f4] => (fn x => checktimer (opf (f1 x, f2 x, f3 x, f4 x)))
  | _ => raise ERR "mk_quadf" ""


fun mk_quintf2 opf fl = case fl of
   [f1,f2,f3,f4,f5] => (fn x => checktimer (opf (f1, f2, f3 x, f4 x, f5 x)))
  | _ => raise ERR "mk_quintf2" ""

fun mk_quintf3 opf fl = case fl of
   [f1,f2,f3,f4,f5] => (fn x => checktimer (opf (f1, f2, f3, f4 x, f5 x)))
  | _ => raise ERR "mk_quintf3" ""

(* -------------------------------------------------------------------------
   Basic intructions
   ------------------------------------------------------------------------- *)


local open IntInf in  

val zero_f = mk_nullf (fn (x,y) => [azero])
val one_f = mk_nullf (fn (x,y) => [aone])
val two_f = mk_nullf (fn (x,y) => [atwo])
val x_f = mk_nullf (fn (x,y) => x)
val y_f = mk_nullf (fn (x,y) => y)
val n_f = mk_nullf (fn (x,y) => [!n_glob])

fun mk_e f (l1,l2) = case (l1,l2) of
    ([],_) => raise Empty
  | (_,[]) => raise Empty
  | (a1 :: m1, a2 :: m2) => (f (a1,a2) :: m1)
  
val addi_f = mk_binfadd 1 (mk_e (op +))
val diff_f = mk_binfadd 1 (mk_e (op -))
val mult_f = mk_binfmult 1 (mk_e (op *))
val divi_f = mk_binfmult 5 (mk_e (op div))
val modu_f = mk_binfmult 5 (mk_e (op mod))

end


fun cond_f fl = case fl of
    [f1,f2,f3] => 
    (fn x => checktimer (if hd (f1 x) <= azero then f2 x else f3 x))
  | _ => raise ERR "mk_condf" ""


fun push_f fl = case fl of
    [f1,f2] => 
    (fn x => (
             incr push_counter; 
             if !push_counter > push_limit then raise Empty else ();
             checktimer (hd (f1 x) :: (f2 x))
             )
             )
  | _ => raise ERR "mk_pushf" ""

fun pop_f fl = case fl of
   [f] => 
   (
   fn x => 
     let val y = case f x of [] => raise Empty | [a] => [a] | a :: m => m in
       checktimer y
     end
   )
  | _ => raise ERR "mk_popf" ""

(* -------------------------------------------------------------------------
   Loop with memory
   ------------------------------------------------------------------------- *)

fun helperm_loop mem f1 f2 n ncur x1 x2 = 
  if ncur >= n then x1 else
  let 
    val (newx1,newx2) = (f1 (x1,x2),f2 (x1,x2)) 
    val newncur = ncur + 1
  in
    store_mem (mem,newncur,(newx1,newx2));
    helperm_loop mem f1 f2 n newncur newx1 newx2
  end
 
fun helperm (mema,memn) f1 f2 n x1 x2 =
  if n < 0 then x1 else 
  if n < !memn then fst (Array.sub (!mema,n)) else
  if !memn <= 0 then 
    (store_mem ((mema,memn),0,(x1,x2));
     helperm_loop (mema,memn) f1 f2 n 0 x1 x2)
  else
  let 
    val lastn = !memn - 1
    val (newx1,newx2) = Array.sub (!mema,lastn) 
  in
    helperm_loop (mema,memn) f1 f2 n lastn newx1 newx2
  end

fun loop2m_f_aux () = 
  let 
    val mema = get_mem ()
    val memn = ref 0
    val mem = (mema,memn)
  in 
    fn (f1,f2,n,x1,x2) => helperm mem f1 f2 (IntInf.toInt (hd n)) x1 x2
  end

fun loop2m_f () = mk_quintf2 (loop2m_f_aux ())

fun loopm_f_aux () =
  let
    val mema = get_mem ()
    val memn = ref 0
    val mem = (mema,memn)
    fun f2 (x1,x2) = [aincr (hd x2)]
  in
    fn (f1,n,x1) => helperm mem f1 f2 (IntInf.toInt (hd n)) x1 [aone]
  end
  
fun loopm_f () = mk_ternf1 (loopm_f_aux ())


(* -------------------------------------------------------------------------
   For loop
   ------------------------------------------------------------------------- *)

fun helper f1 f2 n x1 x2 = 
  if n <= azero then x1 else 
  helper f1 f2 (adecr n) (f1 (x1,x2)) (f2 (x1,x2))

fun loop2_f_aux (f1,f2,n,x1,x2) = helper f1 f2 (hd n) x1 x2
val loop2_f = mk_quintf2 loop2_f_aux

fun loop_f_aux (f1,n,x1) = 
  helper f1 (fn (x1,x2) => [aincr (hd x2)]) (hd n) x1 [aone]
val loop_f = mk_ternf1 loop_f_aux

(* this loop is not memoized *)
fun helpersnd f1 f2 n x1 x2 = 
  if n <= azero then x2 else 
  helpersnd f1 f2 (adecr n) (f1 (x1,x2)) (f2 (x1,x2))

fun loop2snd_f_aux (f1,f2,n,x1,x2) = helpersnd f1 f2 (hd n) x1 x2
val loop2snd_f = mk_quintf2 loop2snd_f_aux

(* -------------------------------------------------------------------------
   While Loop
   ------------------------------------------------------------------------- *)

fun whelper f1 f2 f3 x1 x2 = 
  if hd (f3 (x1,x2)) <= azero then x1 else 
  whelper f1 f2 f3 (f1 (x1,x2)) (f2 (x1,x2))

fun while2_f_aux (f1,f2,f3,x1,x2) = whelper f1 f2 f3 x1 x2
val while2_f = mk_quintf3 while2_f_aux

(* -------------------------------------------------------------------------
   Comprehension
   ------------------------------------------------------------------------- *)

fun sincr x = [aincr (hd x)]

(* find the next element satisfying f starting at x *)
fun compr_next f x =
  if hd (f (x,[azero])) <= azero then x else 
  compr_next f (sincr x)

(* i and x starts at -1 *)           
fun compr_loop mem f n i x =
  if i >= n then x else 
  let 
    val newx = compr_next f (sincr x)
    val newi = i+1
  in
    store_mem (mem,newi,(newx,empty_infl)); 
    compr_loop mem f n newi newx
  end
   
val comprstart = [IntInf.fromInt (~1)]   
      
fun compr_wrap f =
  let
    val mema = get_mem ()
    val memn = ref 0
    fun newf n =
      if n < 0 then raise Div else
      if n < !memn then fst (Array.sub (!mema,n)) else 
      if !memn <= 0 then compr_loop (mema,memn) f n (~1) comprstart else
      let 
        val i = !memn - 1
        val x = fst (Array.sub (!mema,i)) 
      in
        compr_loop (mema,memn) f n i x
      end
  in
    newf
  end

fun compr_f fl = case fl of
    [f1,f2] =>
    let val f1' = compr_wrap f1 in
      (
      fn x =>
      let val y = f1' (IntInf.toInt (hd (f2 x))) in
        checktimer y
      end
      )
    end
  | _ => raise ERR "compr_f" ""

(* -------------------------------------------------------------------------
   Back function when matching
   ------------------------------------------------------------------------- *)

val backl_default = map IntInf.fromInt
  [~57, 19, ~58, 100, ~46, 0, 39, 82, 89, 1, 81, ~83, 49, 94, 59, 55]
val backv_default = Vector.fromList backl_default

val backv_glob = ref (Vector.tabulate (1,fn _ => azero))

fun back_f_aux al = 
  let val a = hd al in
    if a < azero then [azero] 
    else if a >= IntInf.fromInt (Vector.length (!backv_glob)) then raise Div
    else [Vector.sub (!backv_glob, IntInf.toInt a)]
  end
val back_f = mk_unf back_f_aux

(* -------------------------------------------------------------------------
   arcagi primitives
   ------------------------------------------------------------------------- *)

fun in_mati (a,b) = 
  let val (dima,dimb) = !dimi_glob in
    azero <= a andalso a < dima andalso azero <= b andalso b < dimb
  end 

fun equalcolor (a',b',c',d') = 
  let val (a,b,c,d) = (hd a', hd b', hd c', hd d') in
    if not (in_mati (a,b) andalso in_mati (c,d)) then [aonem]
    else if Array2.sub (!mati_glob, IntInf.toInt a, IntInf.toInt b) = 
            Array2.sub (!mati_glob, IntInf.toInt c, IntInf.toInt d) 
      then [aone] else [azero]
  end
  
val equalcolor_f = mk_quadf equalcolor

fun is_out (a',b') = 
  let val (a,b) = (hd a', hd b') in
    if not (in_mati (a,b)) then [aone] else [azero]
  end
  
fun is_colori (a',b',c') = 
  let val (a,b,c) = (hd a', hd b',hd c') in
    if not (in_mati (a,b)) 
      then [aonem] else
    if c < IntInf.fromInt 0 orelse c >= 
       IntInf.fromInt (Vector.length (!coliv_glob))
      then [aonem] else
    if Array2.sub (!mati_glob, IntInf.toInt a, IntInf.toInt b) = 
       Vector.sub (!coliv_glob, IntInf.toInt c)
    then [aone] else [azero]
  end
  
fun is_equal (a,b) = if hd a = hd b then [aone] else [azero]

val is_out_f = mk_binf is_out
val is_colori_f = mk_ternf is_colori
val is_equal_f = mk_binf is_equal

val input_height_f = mk_nullf (fn (x,y) => [fst (!dimi_glob)])
val input_width_f = mk_nullf (fn (x,y) => [snd (!dimi_glob)])
val common_height_f = mk_nullf (fn (x,y) => [fst (!dimo_glob)])
val common_width_f = mk_nullf (fn (x,y) => [snd (!dimo_glob)])

(* -------------------------------------------------------------------------
   Instruction sets
   ------------------------------------------------------------------------- *)

val org_execl = 
  if !rams_noloop then
    [zero_f, one_f, two_f, addi_f, diff_f, mult_f, divi_f, modu_f, cond_f, x_f, 
     y_f]
  else if !rams_short then
    [zero_f, one_f, two_f, addi_f, diff_f, mult_f, divi_f, modu_f, cond_f,
     loop_f, x_f, y_f, n_f, loop2_f]
  else
    [zero_f, one_f, two_f, addi_f, diff_f, mult_f, divi_f, modu_f, cond_f,
     loop_f, x_f, y_f, compr_f, loop2_f]

val arcagi_extra = [equalcolor_f, is_out_f, is_colori_f, is_equal_f,   input_height_f, input_width_f, common_height_f, common_width_f] 
   
val smt_extra = [loop2snd_f] 

val execv = 
  if !rams_nicer 
  then Vector.fromList [one_f, two_f, addi_f, diff_f, mult_f, divi_f, modu_f, 
    x_f, y_f]
  else if !smt_flag
    then Vector.fromList (org_execl @ [push_f, pop_f] @ smt_extra)
  else if !arcagi_flag 
    then Vector.fromList (org_execl @ [push_f, pop_f] @ arcagi_extra)
  else if !matchback_flag
    then Vector.fromList (org_execl @ [push_f, pop_f, back_f])
  else Vector.fromList (org_execl @ [push_f, pop_f])

(* -------------------------------------------------------------------------
   Creates executable for a program
   ------------------------------------------------------------------------- *)

fun wrap_const f =
  let 
    val bref = ref false
    val yref = ref empty_infl
    fun newf x =  
      if !bref then checktimer (!yref) else 
      let val y = f x in bref := true; yref := y; y end
  in
    newf
  end

fun wrap_loop p id fl = case p of
    Insb (9,b,[p1,p2,p3]) =>
    if not b andalso is_const p3 
    then (loopm_f ()) fl
    else Vector.sub (execv,id) fl
  | Insb (13,b,[p1,p2,p3,p4,p5]) =>
    if not b andalso is_const p4 andalso is_const p5 
    then (loop2m_f ()) fl
    else Vector.sub (execv,id) fl
  | _ => Vector.sub (execv,id) fl
  
fun mk_exec_loop (p as (Insb (id,b,pl))) = 
  let 
    val fl = map mk_exec_loop pl 
    val f1 = wrap_loop p id fl
    val f2 = if b then wrap_const f1 else f1
  in 
    f2
  end
  
fun mk_exec p =  mk_exec_loop (mk_progb p)

fun mk_exec_onev p = 
  let val exec = mk_exec p in (fn x => hd (exec ([x],[azero]))) end

fun mk_exec_twov p = 
  let val exec = mk_exec p in (fn (x,y) => hd (exec ([x],[y]))) end

fun coverf_oeis exec =
  let fun g x = hd (exec ([x], [azero])) in 
    scover_oeis g 
  end

(* -------------------------------------------------------------------------
   Enumeration of y programs
   ------------------------------------------------------------------------- *)

val twop = Ins(2,[]);
fun addp a b = Ins(3,[a,b]);
fun mulp a b = Ins(5,[a,b]);

fun program_of_number i = 
  if i < 0 then raise ERR "program_of_number" "negative" 
  else if i < 2 then Ins(i,[])
  else addp (mulp twop (program_of_number (i div 2))) (Ins(i mod 2,[]))
   
fun subst_y p (Ins (id,pl)) =
  if id = y_id then p else Ins(id, map (subst_y p) pl)

fun cover_yenum p =
  let 
    val _ = init_timer ()
    val r = ref []
    fun loop n limit = 
      if n > limit orelse !abstimer > !timelimit then () else
      let 
        val newp = subst_y (program_of_number n) p 
        val exec = mk_exec newp
        val atl = coverf_oeis exec
      in
        r := (n,atl) :: !r; loop (n+1) limit
      end
  in
    if depend_on_y p then loop 0 1000 else loop 0 0;
    filter (not o null o snd) (rev (!r))
  end;

fun coverp_oeis p = 
  if !yenum_flag then 
    let 
      val rl = cover_yenum p 
      val anuml = mk_fast_set Int.compare (map fst (List.concat (map snd rl)))
      val sc = length anuml
    in 
      map (fn x => (x, 1000 - sc)) anuml
    end
  else coverf_oeis (mk_exec p)
 
(* -------------------------------------------------------------------------
   Verifiy cover
   ------------------------------------------------------------------------- *)

fun penum_aux p n = 
  let 
    (* val _ = undol := [] *)
    val f = mk_exec_onev p
    val _ = init_timer ()
    val l = ref []
    fun loop i x = if i >= n then () else
      (
      l := f x :: !l; 
      incr_timer ();
      loop (i+1) (aincr x)
      )
    val _ = catch_perror (loop 0) azero (fn () => ())
  in  
    (* app (fn f => f ()) (!undol); *)
    rev (!l)
  end
  
fun check_conflict v p = 
  let 
    (* val _ = undol := [] *)
    val f = mk_exec_onev p
    fun test x = 
      let val (r,msg) = (f x,"result") handle 
         Empty => (azero,"empty")
       | Div => (azero,"div")
       | ProgTimeout => (azero,"timeout")
       | Overflow => (azero,"overflow")
      in
        if msg <> "result" then msg
        else if not (r = Vector.sub (v,IntInf.toInt x)) then "match"
        else "continue"
      end
    val _ = init_timer ()
    fun loop x = 
      if IntInf.toInt x >= Vector.length v then (x,"success") else
      let val msg = test x in
        if msg <> "continue" then (x,msg)  
        else (incr_timer (); loop (aincr x))
      end
  in  
    loop azero
  end  
  
  
fun penum_wtime r p n = (timeincr := r; penum_aux p n) 
  
fun verify_wtime r (anum,p) = 
  let 
    val seq1 = valOf (Array.sub (bloom.oseq, anum)) 
    val seq2 = penum_wtime r p (length seq1)
  in
    (seq1 = seq2, is_prefix seq2 seq1)
  end

fun verify_file tim file = 
  let 
    val itsol = read_itprogl file
    val isol = map (fn (x,(_,y)) => (x,y)) (distrib itsol) 
    val _ = print_endline ("solutions: " ^ its (length isol))
    val (bbl,t) = add_time (map_assoc (verify_wtime tim)) isol
    val lbad1 = filter (not o fst o snd) bbl
    val lbad2 = filter (not o snd o snd) bbl
  in 
    print_endline 
      (rts_round 4 t ^ ": " ^ its (length lbad1) ^ " " ^ its (length lbad2));
    map fst lbad1
  end

(* -------------------------------------------------------------------------
   Parallel execution (on reversed input?)
   ------------------------------------------------------------------------- *)

val terms_glob = 20
val timeout_glob = 100000

fun execspec_fun file =
  let 
    val log = print_endline
    val dir = selfdir ^ "/exp/seqhash"
    val progdir = dir ^ "/prog"
    val seqdir = dir ^ "/seq"
    val seqpredir = dir ^ "/seqpre"
    val filename = OS.Path.file file
    val progfilegz = progdir ^ "/" ^ filename
    val progfile = OS.Path.base progfilegz
    val cmd1 = "cp " ^ file ^ " " ^ progfilegz
    val _ = cmd_in_dir progdir cmd1
    val cmd2 = "gunzip " ^ progfilegz
    val _ = cmd_in_dir progdir cmd2
    val (sl,t1) = add_time readl progfile
    val _ = remove_file progfile
    val _ = log ("programs: " ^ its (length sl))
    val (pl,t2) = add_time (mapfilter prog_of_gpt_err) sl
    val _ = log ("parsed: " ^ its (length pl)) 
    fun f p = 
      let val seq = penum_wtime timeout_glob p terms_glob in
        if length seq < 2 then NONE else 
        let
          val seqs = string_of_seq seq
          val hm = hashMod 1000000 seqs
          val ht = hm mod 1000
          val s = its hm ^ " | " ^ seqs ^ " | " ^ gpt_of_prog p
        in
          SOME s
        end
      end
  in
    writel (seqpredir ^ "/" ^ (OS.Path.base filename)) (List.mapPartial f pl)
  end

fun write_string file s = writel file [s]
fun read_string file = hd (readl file)
fun write_int file i = writel file [its i]
fun read_int file = string_to_int (hd (readl file))
fun write_unit file () = ()
fun read_unit file = ()

val execspec : (unit,string,unit) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "exec_memo.execspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = let fun f param pl = execspec_fun pl in f end,
  write_param = write_unit,
  read_param = read_unit,
  write_arg = write_string,
  read_arg = read_string,
  write_result = write_unit,
  read_result = read_unit
  }

fun bare_readl_app f path =
  let
    val file = TextIO.openIn path
    fun loop file = case TextIO.inputLine file of
        SOME line => (f line; loop file)
      | NONE => ()
  in
    loop file; TextIO.closeIn file
  end;

fun bare_appendl file sl =
  let val oc = TextIO.openAppend file in
    app (fn s => TextIO.output (oc,s)) sl;
    TextIO.closeOut oc
  end

fun merge_seqpre () =
  let
    val dir = selfdir ^ "/exp/seqhash/seqpre"
    val filel = map (fn x => dir ^ "/" ^ x) (listDir dir)
    val array_glob = Array.tabulate (1000, fn _ => []:string list)
    fun f s =
      let 
        val (s1,_,_) = triple_of_list (String.tokens (fn x => x = #"|") s)
        val h = string_to_int s1 mod 1000
      in
        Array.update (array_glob, h, s :: Array.sub (array_glob,h))
      end
    val _ = app (bare_readl_app f) filel
    fun seq_file i = selfdir ^ "/exp/seqhash/seq/" ^ its i;
    val _ = List.tabulate (1000, 
      fn i => bare_appendl (seq_file i) (Array.sub (array_glob,i)))
  in
    app remove_file filel
  end
  
fun parallel_exec ncore filel =
  let
    val dir = selfdir ^ "/exp/seqhash"
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = mkDir_err dir
    val _ = mkDir_err (dir ^ "/seq")
    val _ = mkDir_err (dir ^ "/prog")
    fun log s = (print_endline s; append_endline (dir ^ "/log") s)
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val (_,t) = add_time
      (smlParallel.parmap_queue_extern ncore execspec ()) filel
    val _ = log ("compute time: " ^ rts_round 2 t)
    val (_,t) = add_time merge_seqpre ()
  in
    log ("merge time: " ^ rts_round 2 t)
  end

(* -------------------------------------------------------------------------
   Producing sequences and hashing them
   ------------------------------------------------------------------------- *)

fun seqhash_init inputdir =
  let 
    val sl1 = listDir inputdir
    val sl2 = filter (fn x => String.isSuffix ".gz" x) sl1
    val sl3 = dict_sort String.compare sl2
    val sl4 = map (fn x => inputdir ^ "/" ^ x) sl3
  in
    sl4
  end;

fun seqhash_loop ncore suffix remainingl = 
  if null remainingl then () else
  let 
    val _ = print_endline (its (length remainingl) ^ " remaining files")
    val (currentl,newremainingl) = part_n 1000 remainingl 
    val _ = parallel_exec ncore currentl
    val _ = appendl (selfdir ^ "/exp/seqhash/done_" ^ suffix) currentl
  in
    seqhash_loop ncore suffix newremainingl
  end;

(*
mkdir /scratch/thibault/seqpre
ln -s /scratch/thibault/seqpre seqpre
mkdir /scratch/thibault/prog
ln -s /scratch/thibault/prog prog 
mkdir /scratch/thibault/seq
ln -s /scratch/thibault/seq seq
*)

(*
load "exec_memo"; open aiLib kernel exec_memo;

val dir = "/home/mptp/nfs/oe2/bcksol-air03__fnv";
val dirl = listDir dir;

"fnv600s", "fnv1", "fnv500s", "fnv2", "fnv", 
"fnv700s", "fnv501_539", "fnv457_516"
val dirname = List.nth (dirl,4);
val inputdir = dir ^ "/" ^ dirname;
val remainingl = seqhash_init inputdir; length remainingl; (* 198000 *)
seqhash_loop 40 dirname remainingl;

mkdir /scratch/thibault/seq_fnv700s_gz
ln -s /scratch/thibault/seq_fnv700s_gz seq_fnv700s_gz
ls seq | parallel -j 10 'sort -u seq/{} | gzip > seq_fnv700s_gz/{}.gz'
(* remove files in seq without removing the linked directory *)

*)

(* -------------------------------------------------------------------------
   Sorting sequences by their prefix (fixed directory)
   ------------------------------------------------------------------------- *)

val expdir = selfdir ^ "/exp/seqhash"
val sortdir = selfdir ^ "/exp/seqhash/sort"

(* batching *)
fun create_batch_aux (lim1,lim2) skip (batch,acci) l = 
  if acci > lim1 then ((rev batch,acci), rev skip, l) else
  (
  case l of 
    [] => ((rev batch,acci), rev skip, l)
  | a :: m =>     
    if acci + snd a > lim2 
    then create_batch_aux (lim1,lim2) (a :: skip) (batch,acci) m
    else create_batch_aux (lim1,lim2) skip (a :: batch, acci + snd a) m
  )
  ;
  
fun create_batchl (lim1,lim2) l = case l of 
    [] => [] 
  | a :: m => 
    let val (batch,skip,cont) = 
      create_batch_aux (lim1,lim2) [] ([a],snd a) m
    in
      batch :: create_batchl (lim1,lim2) (skip @ cont)
    end;   

fun create_batch_fixed () = 
  let 
    val sl0 = readl (expdir ^ "/tree")
    val sl1 = map (split_pair #" ") sl0
    val sl2 = map_snd string_to_int sl1
    val batchl = create_batchl (5000000,10000000) sl2
    val _ = print_endline ("batch: " ^ its (length batchl))
  in
    batchl
  end

fun output_treebatch_fixed () =
  let
    val batchl = create_batch_fixed ()
    fun f (l,_) = 
       let val s = fst (hd l) in
         map (fn s' => (s',s)) (map fst l)
       end;
    val batchsl = List.concat (map f batchl)
    val sl = map (fn (a,b) => a ^ " " ^ b) batchsl
  in
    writel (expdir ^ "/treebatch") sl
  end
  


(* character *) 
fun string_subo (s,i) = SOME (String.sub (s,i)) handle Subscript => NONE;
fun its_ i = if i = 10 then "_" else its i
fun cti_ c = if c = #"_" then 10 else string_to_int (Char.toString c)

fun next_int (s,i) = case string_subo (s,i) of 
    SOME c => if Char.isDigit c
              then (string_to_int (Char.toString c), i+1)
              else next_int (s,i+1)
  | NONE => (10,i+1);  
  
fun after_char_aux ctop (s,i) = case string_subo (s,i) of 
    SOME c => if c = ctop
              then i+1
              else after_char_aux ctop (s,i+1)
  | NONE => raise ERR "after_char_aux" s;

fun after_char ctop s = after_char_aux ctop (s,0);


(* tree *)
datatype tree = Node of tree vector | Leaf of (TextIO.outstream * int ref);  

fun read_tree_aux d prefix =
  if dmem prefix d 
    then Leaf (dfind prefix d)
  else if dmem (prefix ^ "_") d then 
    let 
      fun f i = read_tree_aux d (prefix ^ its_ i)
      val v = Vector.tabulate (11,f)
    in
      Node v
    end
  else raise ERR "read_tree_aux" prefix;

fun read_tree d = read_tree_aux d "";

fun output_leaf_aux tree (s,i) = case tree of 
    Leaf (oc,counter) => 
      (
      TextIO.output (oc,s); 
      incr counter; 
      if !counter > 1000 then (TextIO.flushOut oc; counter := 0) else ()
      )
  | Node v => 
    let val (pathe,newi) = next_int (s,i) in
      output_leaf_aux (Vector.sub (v,pathe)) (s,newi) 
    end;

fun output_leaf s tree = output_leaf_aux tree (s, after_char #"|" s);
  

(* sorting function *)
fun mk_all_dir batchl = 
  app (fn (x,_) => mkDir_err (sortdir ^ "/" ^ fst (hd x))) batchl

fun sort_file file_gz =
  let
    val batchl = create_batch_fixed ()
    fun log s = print_endline s
    val _ = log ("file: " ^ file_gz)
    val name = OS.Path.base (OS.Path.file file_gz) ^ "_" ^ 
               OS.Path.file (OS.Path.dir file_gz);
    fun f1 (x,_) = 
      TextIO.openAppend (sortdir ^ "/" ^ fst (hd x) ^ "/" ^ name)
    val ocl = map_assoc f1 batchl
    fun clean () = app (fn (_,oc) => TextIO.closeOut oc) ocl;
    fun f2 ((namel,_),oc) = 
      map (fn (name,_) => let val i = ref 0 in (name, (oc,i)) end) namel;
    val dtop = dnew String.compare (List.concat (map f2 ocl))
    val treetop = read_tree dtop
    val temp = expdir ^ "/sortpre/" ^ name
    val cmd = "gunzip -c " ^ file_gz ^ " > " ^ temp
    val (_,t) = add_time (cmd_in_dir expdir) cmd
    val _ = log ("unzip: " ^ rts_round 2 t)
    fun f3 s = output_leaf s treetop;
    val (_,t) = add_time (bare_readl_app f3) temp
    val _ = log ("sort: " ^ rts_round 2 t)
  in
    remove_file temp; clean (); file_gz
  end

fun compress_dir expnamedir =
  let
    val (expname,dir) = split_pair #":" expnamedir 
    val filel0 = listDir dir
    val filel1 = filter (fn x => not (String.isSuffix ".gz" x)) filel0
    val filel2 = map (fn x => (dir ^ "/" ^ x)) filel1
    val outputfile = dir ^ "/" ^ expname ^ ".gz"
    val cmd = "cat " ^ String.concatWith " " filel2 ^ 
      " | gzip > " ^ outputfile;
    val _ = cmd_in_dir dir cmd
    val _ = app remove_file filel2
  in
    expnamedir
  end

(* create directories
mkdir /scratch/thibault
mkdir /scratch/thibault/sortpre
ln -s /scratch/thibault/sortpre sortpre
mkdir /scratch/thibault/sort
ln -s /scratch/thibault/sort sort

*)

(* copy
"fnv600s", "fnv1", "fnv500s", "fnv2", "fnv", 
"fnv700s", "fnv501_539", "fnv457_516"
scp -r 10.35.125.79:~/oeis-synthesis/src/exp/seqhash/seq_fnv500s_gz seq_fnv500s_gz
*)  

(* sort
load "exec_memo"; open kernel aiLib exec_memo;
mk_all_dir (create_batch_fixed ());
val expdir = selfdir ^ "/exp/seqhash";
val dir = expdir ^ "/seq_fnv600s_gz";
val filel = map (fn x => dir ^ "/" ^ x) (listDir dir);
val (rl,t) = add_time (parmap_sl 10 "exec_memo.sort_file") filel;
*)

(* gzip
load "exec_memo"; open kernel aiLib exec_memo;
val sortdir = selfdir ^ "/exp/seqhash/sort";
val dirl = listDir sortdir;
val expname = "fnv600s";
val expnamedirl = map (fn x => expname ^ ":" ^ x) dirl;
val (rl,t) = add_time (parmap_sl 10 "exec_memo.compress_dir") expnamedirl;
*)






(* -------------------------------------------------------------------------
   Parallel checking with b-files
   ------------------------------------------------------------------------- *)

fun get_bseq_aux i acc sl = case sl of 
    [] => (rev acc, "full")
  | s :: m =>
    let 
      val (s1,s2) = pair_of_list 
      (first_n 2 (String.tokens Char.isSpace s))
      val i1 = valOf (IntInf.fromString s1)
      val i' = if i = 0 then IntInf.toInt i1 else i      
    in
      if IntInf.fromInt i' <> i1 
        then raise ERR "index error" (its i' ^ " " ^ s1) 
      else if String.size s2 > 1000
        then (rev acc, "maxi") 
      else get_bseq_aux (i'+1) (valOf (IntInf.fromString s2) :: acc) m
    end;
    
fun get_bseq sl = get_bseq_aux 0 [] sl;    

val bdir = selfdir ^ "/data/oeis-bfile"

fun read_bseq a =
  let 
    val sl0 = readl (bdir ^ "/b" ^ its a ^ ".txt")
    val sl1 = filter (fn s => not (all Char.isSpace (explode s) orelse 
       String.isPrefix "#" s)) sl0
  in
    get_bseq sl1
  end

fun check_bfile (a,pl) =
  let 
    val aseq = valOf (Array.sub (oseq,a))
    val (bseq,msg) = read_bseq a
    val msg' = if aseq = bseq then "Equal" 
               else if is_prefix aseq bseq then msg else "NotPrefix"
    val seqmsg = String.concatWith " " 
      ["A" ^ its a, its (length aseq), its (length bseq), msg'] 
    val v = Vector.fromList bseq
  in
    if mem msg' ["Equal","NotPrefix"] then seqmsg else
    let 
      val rl = map_assoc (check_conflict v) pl
      fun f (p,(i,s)) = s ^ " " ^ infts i
      val msgl = map f rl
      val summary = 
        if exists (fn (p,(i,s)) => s = "success") rl then "Success" else 
        if exists (fn (p,(i,s)) => s = "timeout") rl then "Timeout"
        else "Failure"
    in
      String.concatWith " | " (summary :: seqmsg :: msgl)
    end 
  end

fun write_int file i = writel file [its i]
fun read_int file = string_to_int (hd (readl file))

fun string_of_apl (anum,pl) = 
  its anum ^ "," ^ String.concatWith "," (map gpt_of_prog pl)

fun apl_of_string s =
  let val sl = String.tokens (fn x => x = #",") s in
    (string_to_int (hd sl), map prog_of_gpt (tl sl))
  end
  
fun write_apl file apl = writel file [string_of_apl apl]
fun read_apl file = apl_of_string (hd (readl file))
fun write_string file s = writel file [s]
fun read_string file = hd (readl file)


val bcheckspec : (unit, int * prog list, string) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "exec_memo.bcheckspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = let fun f () anum = check_bfile anum in f end,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = write_apl,
  read_arg = read_apl,
  write_result = write_string,
  read_result = read_string
  }

fun exists_bfile x = 
  let val file = bdir ^ "/b" ^ its x ^ ".txt" in exists_file file end;

fun parallel_bcheck ncore expname =
  let  
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = mkDir_err dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000) 
    val _ = smlExecScripts.buildheap_dir := dir
    val sol1 = read_itprogl (dir ^ "/input")
    val sol2 = map_snd (map snd) sol1
    val _ = writel (dir ^ "/log") ["sol: " ^ its (length sol1)];
    fun f (a,pl) = if exists_bfile a then SOME (a,pl) else NONE
    val apl = List.mapPartial f sol2
    val _ = append_endline (dir ^ "/log") ("bfile: " ^ its (length apl));
    val (sl,t) = add_time 
      (smlParallel.parmap_queue_extern ncore bcheckspec ()) apl
  in
    append_endline (dir ^ "/log") ("time: " ^ rts t);
    writel (dir ^ "/output") sl
  end

end (* struct *)


(* -------------------------------------------------------------------------
   Verifying that new code accept old solutions
   ------------------------------------------------------------------------- *)

(*
PolyML.print_depth 10;
load "human"; open human;
load "exec_memo";  open kernel aiLib exec_memo;
val badl = verify_file 1000000 (selfdir ^ "/model/itsol209");
val badl = verify_file 1000000 (selfdir ^ "/exp/intl3/hist/itsol2088");


val itsol = read_itprogl file
val isol = map (fn (x,(_,y)) => (x,y)) (distrib itsol);
val _ = print_endline ("solutions: " ^ its (length isol));


fun get_bad isol = case isol of 
    [] => NONE
  | a :: m => 
    if ((verify_wtime 100000 a; false) handle Option => true)
    then SOME a
    else get_bad m
    
val (anum,p) = valOf (get_bad isol);
val (bbl,t) = add_time (map_assoc (verify_wtime tim)) isol
val lbad1 = filter (not o fst o snd) bbl
val lbad2 = filter (not o snd o snd) bbl


val file = (selfdir ^ "/exp/intl3/hist/itsol2088");
val read_itprogl 
*)

(* -------------------------------------------------------------------------
   Testing
   ------------------------------------------------------------------------- *) 
    
(* 
load "exec_memo"; open exec_memo; 
load "human"; open kernel human aiLib;

val p =  parse_human "(loop ( * 2 x) x 1)";
val p = parse_human "(% x 2)";
val p = parse_human "(% (- (loop ( * 2 x) x 1) 2) x) "; 
val p =  parse_human "(loop ( * 2 x) x 1)";
val p = parse_human "(loop ( * x x) x 2)";

val p =  parse_human "(- (loop ( * 2 x) x 1) (loop ( * 2 x) x 1))";
val (anum,p) = hd lbad;
val seq = valOf (Array.sub (bloom.oseq, anum));
humanf p;


val p = parse_human "(loop2 (+ x y) x x 2 1)";

abstimer := 0;
val f = mk_exec_onev p;
f 100;
timeincr := 100000000;
!abstimer;

val (l1,t) = add_time (penum_wtime 1000000 p) (length seq);
!abstimer;
*)  

(* -------------------------------------------------------------------------
   Checking solutions against b-files
   ------------------------------------------------------------------------- *) 

(* 
load "exec_memo"; open exec_memo;
parallel_bcheck 40 "bfile2";

cd exp/bfile1

wc -l output
grep -r "Equal" output | wc -l
grep -r "NotPrefix" output | wc -l

grep -r "Success" output | wc -l
grep -r "Timeout" output | wc -l
grep -r "Failure" output | wc -l


*)




