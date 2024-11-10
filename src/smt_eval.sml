structure smt_eval :> smt_eval =
struct

open aiLib dir kernel sexp progx smt_hol smt_progx
val ERR = mk_HOL_ERR "smt_eval"
type progx = progx.progx

(* --------------------------------------------------------------------------
   An extra function is created for the second higher argument of loop2
   -------------------------------------------------------------------------- *)

fun add_loop2snd_one px = case px of
    Insx((13,SOME s),argl) => [px, Insx((16, SOME ("s" ^ tl_string s)),argl)]
  | _ => [px]
  
fun add_loop2snd pxl = mk_fast_set progx_compare 
  (List.concat (map add_loop2snd_one pxl));

fun all_subprog_extra px =
  add_loop2snd (mk_fast_set progx_compare (all_subprog px))


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
    val arity = if depend_on_z p then raise ERR "fenum_px" ""
                else if depend_on_y p then 2 
                else if depend_on_x p then 1 else 0
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

fun subprog_equalities (smallxx,fastxx) =
  let
    val (smallpl,fastpl) = (all_subprog_extra smallxx, all_subprog_extra fastxx)
    val (smalle,faste) = (fingerprint_pxl smallpl, fingerprint_pxl fastpl)
    val d = ref (dempty fingerprint_cmp)
    fun fsmall (progx,seq) = 
      let 
        val (oldsmall,oldfast) = 
          case dfindo seq (!d) of NONE => ([],[]) | SOME x => x
        val newsmall = progx :: oldsmall 
      in
        d := dadd seq (newsmall,oldfast) (!d)
      end
    fun ffast (progx,seq) = 
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
  
(*
load "smt_eval"; open kernel aiLib progx smt_eval;
val (_,(small,fast)) = 
  random_elem (smt_progx.read_anumprogpairs "smt_benchmark_progpairs");
val (smallx,fastx) = progpair_to_progxpair (small,fast);
val smallxx = progx_to_progxx smallx;
val fastxx = progx_to_progxx fastx;
val ppl = subprog_equalities (smallxx,fastxx);

load "human"; open human;
fun f (p1,p2) = humanf (progx_to_prog p1) ^ " | " ^ humanf (progx_to_prog p2);

app print_endline (map f ppl);
*)  
  

end (* struct *)
