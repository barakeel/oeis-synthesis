structure smt_eval :> smt_eval =
struct

open aiLib dir kernel sexp progx
val ERR = mk_HOL_ERR "smt_eval"
type prog = kernel.prog
type progx = progx.progx

(* --------------------------------------------------------------------------
   An extra function is created for the second higher argument of loop2
   -------------------------------------------------------------------------- *)

fun add_loop2snd_one px = case px of
    Insx((13,SOME s),argl) => [px, Insx((16, SOME ("s" ^ tl_string s)),argl)]
  | _ => [px]
  
fun add_loop2snd pxl = mk_fast_set progx_compare 
  (List.concat (map add_loop2snd_one pxl));


(* add_loop2snd temporary removed *)
fun all_subprog_extra px = mk_fast_set progx_compare (all_subprog px)

(* --------------------------------------------------------------------------
   Finger print a program
   -------------------------------------------------------------------------- *)

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

val inputl = 
  let 
    val l1 = List.tabulate (10,IntInf.fromInt)
    val l1b = List.tabulate (15,fn x => IntInf.fromInt (x-5))
  in
    cartesian_product l1 l1b
  end

fun fingerprint_one f x = 
  (
  abstimer := 0; 
  (
  SOME (f x) handle
    Div => NONE
  | ProgTimeout => NONE
  | Overflow => NONE
  | Empty => NONE
  )
  )

fun fingerprint_px px = 
  let 
    val p = progx_to_prog px
    val f = exec_memo.mk_exec_twov p
  in
    map (fingerprint_one f) inputl
  end

fun match_fingerprint_aux (ao,bo) = case (ao,bo) of
    (NONE,_) => true
  | (_,NONE) => true
  | (SOME a, SOME b) => a = b

fun match_fingerprint (fp1,fp2) =
  all match_fingerprint_aux (combine (fp1,fp2))
  handle HOL_ERR _ => raise ERR "match_fingerprint" ""

fun fingerprint_loop (px as Insx (_,pxl)) =
  map fingerprint_px (px :: pxl) 

fun match_loop ((px1,fpl1),(px2,fpl2)) =
  all match_fingerprint (combine (fpl1,fpl2))
  handle HOL_ERR _ => raise ERR "match_loop" ""
  

(*
(* --------------------------------------------------------------------------
   Finger print a program
   -------------------------------------------------------------------------- *)

fun const_seq l = null l orelse all (fn x => x = hd l) l

fun subprog_equalities (smallxx,fastxx) =
  let
    val (smallpl,fastpl) = (all_subprog_extra smallxx, all_subprog_extra fastxx)
    val (smalle,faste) = (fingerprint_pxl smallpl, fingerprint_pxl fastpl)
    val d = ref (dempty fingerprint_cmp)
    fun fsmall (progx,seq) = 
      if const_seq seq then () else
      let 
        val (oldsmall,oldfast) = 
          case dfindo seq (!d) of NONE => ([],[]) | SOME x => x
        val newsmall = progx :: oldsmall 
      in
        d := dadd seq (newsmall,oldfast) (!d)
      end
    fun ffast (progx,seq) = 
      if const_seq seq then () else
      let 
        val (oldsmall,oldfast) = 
          case dfindo seq (!d) of NONE => ([],[]) | SOME x => x
        val newfast = progx :: oldfast
      in
        d := dadd seq (oldsmall,newfast) (!d)
      end    
    val _ = app fsmall smalle
    val _ = app ffast faste
    val l = dlist (!d)
    fun mk_pairs (seq,(progl1,progl2)) = cartesian_product progl1 progl2
  in
    filter (fn (a,b) => progx_to_prog a <> 
                        progx_to_prog b) (List.concat (map mk_pairs l))
  end

(* --------------------------------------------------------------------------
   create subprogram pairs
   -------------------------------------------------------------------------- *)

fun subprog_eq_one (a,(small,fast)) =
  let 
    val (smallx,fastx) = progpair_to_progxpair_shared (small,fast)
    val smallxx = progx_to_progxx smallx
    val fastxx = progx_to_progxx fastx
    fun distribute (a,l) = 
      let fun f (x,i) = (a ^ "_" ^ its i, x) in
        map f (number_snd 0 l) 
      end;
    
  in
    distribute (a, subprog_equalities (smallxx,fastxx))
  end
 
fun contain_loop (Ins(i,pl)) = mem i [9,12,13] orelse 
  exists contain_loop pl 
 
fun subprog_eq_list appl3 =
  let 
    val appl4 = List.concat (map subprog_eq_one appl3)
    val appl6 = map_snd progxpair_to_progpair appl4
    fun test (a,(p1,p2)) = contain_loop p1 orelse contain_loop p2
    val appl7 = filter test appl6
  in
    appl7
  end
*) 
 
(*
load "smt_eval"; load "search_term";
open kernel aiLib progx smt_eval smt_progx search_term;

val appl1 = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs");
val d = enew String.compare 
  (map OS.Path.base (readl "../../oeis-smt/aind_sem"));
val appl2 = filter (fn x => emem (fst x) d) appl1;
val appl3 = filter (good_pp o snd) appl2;

val appl7 = subprog_eq_list appl3;
length appl7;

write_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sub") appl7;
*)  
  
(*


  
writel (selfdir ^ "/proof0_ex") (List.concat (map tonmt rl21));

(* human output *)

load "progx"; open progx;



fun tohuman ((s1,s2),sl) =
  let
    val (p1x,p2x) = progpair_to_progxpair_shared pp
  in 
    ((s1,s2), (progx_to_string p1x, progx_to_string p2x), 
     stringl_to_inductl pp sl)
  end;

val rl21t = map tohuman rl21;






training output (eval input): proof0_cj 
p1=p2>cj1|cj2|cj3|...
training input (eval output): proof0_ex
p1=p2>cj1
p1=p2>cj2
p1=p2>cj3
...

val sel = filter (fn ((a,b),l) => not (b = "unsat" andalso null l)) rl1;
val sel1 = map (fst o fst) sel;
*)



end (* struct *)
