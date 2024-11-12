structure smt_eval :> smt_eval =
struct

open aiLib dir kernel sexp progx smt_hol smt_progx
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


val inputl1 = List.tabulate (20,IntInf.fromInt) 
val inputl1_0 = map (fn x => (x,IntInf.fromInt 0)) inputl1;

val inputl2 = 
  let 
    val l1 = List.tabulate (10,IntInf.fromInt)
    fun cmp ((a,b),(c,d)) = case IntInf.compare (a+b,c+d) of
        EQUAL => list_compare IntInf.compare ([a,b],[c,d])
      | x => x
    val l2 = dict_sort cmp (cartesian_product l1 l1)
  in
    l2
  end;
  
val inputl2neg = 
  let 
    val l1 = List.tabulate (10,IntInf.fromInt)
    val l2 = List.tabulate (9, fn x => IntInf.fromInt ((~1) - x))
    fun cmp ((a,b),(c,d)) = case IntInf.compare (a+b,c+d) of
        EQUAL => list_compare IntInf.compare ([a,b],[c,d])
      | x => x
    val l2 = dict_sort cmp (cartesian_product l1 l2)
  in
    l2
  end;  

fun fenum f xltop =
  let
    fun init () = (abstimer := 0; timelimit := 100000)
    fun loop acc xl = 
      (
      init ();
      if null xl orelse f (hd xl) > maxarb
      then SOME (rev acc)
      else loop (f (hd xl) :: acc) (tl xl)
      )
  in
    loop [] xltop handle
      Div => NONE
    | ProgTimeout => NONE
    | Overflow => NONE
  end;
 
val fingerprint_cmp = list_compare IntInf.compare
 
fun fingerprint_px px = 
  let 
    val p = progx_to_prog px
    val f = exec_memo.mk_exec_twov p
  in
    fenum f inputl2
  end

fun fingerprint_pxl pxl = 
  let 
    fun f px = case fingerprint_px px of 
        NONE => NONE 
      | SOME seq => SOME (px,seq)
  in
    List.mapPartial f pxl
  end

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

fun progx_to_string p = 
  let   
    fun h p = progx_to_string p
    fun sbinop s (p1,p2) = "(" ^ h p1 ^ " " ^ s ^ " " ^ h p2 ^ ")"  
  in
    case p of
      Insx ((0,_),[]) => its 0
    | Insx ((1,_),[]) => its 1
    | Insx ((2,_),[]) => its 2
    | Insx ((3,_),[p1,p2]) => sbinop "+" (p1,p2)
    | Insx ((4,_),[p1,p2]) => sbinop "-" (p1,p2) 
    | Insx ((5,_),[p1,p2]) => sbinop "*" (p1,p2)
    | Insx ((6,_),[p1,p2]) => sbinop "div" (p1,p2)
    | Insx ((7,_),[p1,p2]) => sbinop "mod" (p1,p2)
    | Insx ((8,_),[p1,p2,p3]) => 
      "(if " ^ h p1 ^ " <= 0 then " ^ h p2  ^ " else " ^ h p3 ^ ")"
    | Insx ((id,_),[]) => name_of_oper id
    | Insx ((id,NONE),pl) => 
      "(" ^ String.concatWith " " (name_of_oper id :: map h pl) ^ ")"
    | Insx ((id,SOME s),pl) => 
      "(" ^ String.concatWith " " (name_of_oper id ^ ":" ^ s :: map h pl) ^ ")"  
  end;

fun tohuman ((s1,s2),sl) =
  let 
    val (pp as (p1,p2)) = dfind s1 d1 
    val (p1x,p2x) = progpair_to_progxpair_shared pp
  in 
    ((s1,s2), (progx_to_string p1x, progx_to_string p2x), 
     stringl_to_inductl pp sl)
  end;

val rl21t = map tohuman rl21;

fun tts tm = rm_space
   (String.translate (fn c => if c = #"\n" then " " else str c)
  (term_to_string tm));
fun g ((s1,s2),(s3,s4),tml) = 
  s1 ^ "\n" ^ 
  s3 ^ " = " ^ s4 ^ "\n" ^
  String.concatWith " | " (map tts tml);
  
writel "proof0_human" (map g rl21t);

OS.Process.system ("sed -i 's/\\$var\\$(0)/0/g; s/\\$var\\$(1)/1/g; s/\\$var\\$(2)/2/g' proof0_human");




training output (eval input): proof0_cj 
p1=p2>cj1|cj2|cj3|...
training input (eval output): proof0_ex
p1=p2>cj1
p1=p2>cj2
p1=p2>cj3
...
*)



end (* struct *)
