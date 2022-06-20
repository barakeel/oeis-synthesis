structure exec :> exec =
struct

open HolKernel boolLib aiLib kernel bloom rat
val ERR = mk_HOL_ERR "exec"
type prog = kernel.prog


val aleq = Arbint.<=
val azero = Arbint.zero
val aone = Arbint.one
fun aincr x = Arbint.+ (x,aone)
fun adecr x = Arbint.- (x,aone)

(* -------------------------------------------------------------------------
   Time limit
   ------------------------------------------------------------------------- *)

fun test f x =
  let val y = f x in
    if large_rarb y then raise ProgTimeout
    else if large_rint y then check_timelimit ()
    else 
      if !skip_counter > 1000 
      then (skip_counter := 0; check_timelimit ()) 
      else incr skip_counter
    ;
    y
  end

(* -------------------------------------------------------------------------
   Instructions
   ------------------------------------------------------------------------- *)
 
fun mk_nullf opf fl = case fl of
    [] => (fn x => (test opf x))
  | _ => raise ERR "mk_nullf" ""

fun mk_unf opf fl = case fl of
   [f1] => (fn x => (test opf (f1 x)))
  | _ => raise ERR "mk_unf" ""

fun mk_binf opf fl = case fl of
   [f1,f2] => (fn x => (test opf (f1 x, f2 x)))
  | _ => raise ERR "mk_binf" ""

fun mk_ternf opf fl = case fl of
   [f1,f2,f3] => (fn x => (test opf (f1 x, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf" ""

fun mk_binf1 opf fl = case fl of
   [f1,f2] => (fn x => (test opf (f1, f2 x)))
  | _ => raise ERR "mk_binf1" ""

fun mk_ternf1 opf fl = case fl of
   [f1,f2,f3] => (fn x => (test opf (f1, f2 x, f3 x)))
  | _ => raise ERR "mk_ternf1" ""

fun mk_quintf2 opf fl = case fl of
   [f1,f2,f3,f4,f5] => 
   (fn x => (test opf (f1, f2, f3 x, f4 x, f5 x)))
  | _ => raise ERR "mk_quintf2" ""

(* first-order *)
val zero_f = mk_nullf (fn _ => rzero)
val one_f = mk_nullf (fn _ => rone)
val two_f = mk_nullf (fn _ => rtwo)
val x_f = mk_nullf (fn (x,y) => x)
val y_f = mk_nullf (fn (x,y) => y)
val addi_f = mk_binf raddi
val diff_f = mk_binf rdiff
val mult_f = mk_binf rmult
val divi_f = mk_binf rdivi
val modu_f = mk_binf rmodu
val cond_f = mk_ternf rcond
val condeq_f = mk_ternf rcondeq
val numer_f = mk_unf rnumer
val denom_f = mk_unf rdenom
val divr_f = mk_binf rdivr
val intpart_f = mk_unf rintpart

(* higher-order *)
fun loop_f_aux i f n x = 
  if aleq (n,azero) then x else 
  loop_f_aux (aincr i) f (adecr n) (f (x, mk_rat i))
fun loop_f_aux2 (f,n,x) = loop_f_aux aone f (intpart n) x
val loop_f = mk_ternf1 loop_f_aux2
 
(* compr_f just used as a placeholder *)
val compr_f = x_f
val compreq_f = x_f
fun compr_f_cache v f2 x = 
  let val input = Arbint.toInt (intpart (f2 x)) 
    handle Overflow => raise Div
  in
    if input < 0 orelse input >= Vector.length v 
    then raise Div 
    else test Vector.sub (v,input)
  end  

fun loop2_f_aux f1 f2 n x1 x2 = 
  if aleq (n,azero) then x1 else 
  loop2_f_aux f1 f2 (adecr n) (f1 (x1,x2)) (f2 (x1,x2))
fun loop2_f_aux2 (f1,f2,n,x1,x2) = loop2_f_aux f1 f2 (intpart n) x1 x2
val loop2_f = mk_quintf2 loop2_f_aux2

(* memory operators *)
val mem_glob = ref (Array.array (0, rzero))
fun outofbound x a = x < 0 orelse x >= Array.length a

fun lookup_f fl = case fl of
    [f1] => (fn x => 
         let val z = Arbint.toInt (intpart (f1 x)) in
           if outofbound z (!mem_glob) then raise Div else 
           test Array.sub (!mem_glob,z)
         end)
  | _ => raise ERR "lookup_f" ""

fun assign_f fl = case fl of
   [f1,f2,f3] => 
   (fn x => 
      let fun g y =
        let val z = Arbint.toInt (intpart (f1 y)) in
          if outofbound z (!mem_glob) then raise Div else 
          (Array.update (!mem_glob, z, (f2 y)); f3 y)
        end
      in
        test g x
      end)
  | _ => raise ERR "assign_f" ""
  

(* list all defined operators: should match kernel.sml and human.sml *)

val base_execl = [
  zero_f, one_f, two_f,
  addi_f, diff_f, mult_f, divi_f, modu_f,
  cond_f, loop_f,
  x_f, y_f,
  compr_f, loop2_f,
  condeq_f, compreq_f]
val ratio_execl = [numer_f, denom_f, divr_f, intpart_f] 
val mem_execl = [lookup_f,assign_f]
  
val execv = Vector.fromList (base_execl @ ratio_execl @ mem_execl) 

(* -------------------------------------------------------------------------
   Execute a program on some inputs with auto-initialization of compr
   ------------------------------------------------------------------------- *)

fun mk_exec_aux2 ccache (p as (Ins (id,pl))) = 
  let val fl = map (mk_exec_aux2 ccache) pl in
    if mem id [12,15] then
      let val v = dfind (hd pl, id) ccache handle NotFound =>
        raise ERR "mk_exec_aux2" (raw_prog p)
      in compr_f_cache v (hd (tl fl)) end 
    else (Vector.sub (execv,id) fl
          handle Subscript => raise ERR "mk_exec_aux2" (its id))
  end
   
fun mk_exec_aux ccache p =
  let val f = mk_exec_aux2 ccache p in
    (fn x => (mem_glob := Array.array (!memsize, rzero); f x))
  end


val max_compr_number = 1000

fun add_ccache ccache (p,id) =
  if dmem (p,id) (!ccache) then () else
  let
    val test = if id = 12 then aleq else (op =)
    val _ = init_timer ()
    val f = mk_exec_aux (!ccache) p
    val l = ref []
    fun loop i a =
      if i >= max_compr_number then () else
        if test (fst (f (mk_rat a, rzero)), azero)
        then (l := mk_rat a :: !l; incr_timer (); loop (i+1) (aincr a)) 
        else loop i (aincr a)
    val _ = catch_perror (loop 0) azero (fn () => ())
    val v = Vector.fromList (rev (!l))
  in
    ccache := dadd (p,id) v (!ccache)
  end

fun create_ccache p =
  let 
    val ccache = ref (dempty (cpl_compare prog_compare Int.compare))
    val comprl = dict_sort 
      (cpl_compare prog_compare_size Int.compare) (all_subcompr p)
  in
    app (add_ccache ccache) comprl;
    !ccache
  end

fun mk_exec p = let val ccache = create_ccache p in mk_exec_aux ccache p end

(* -------------------------------------------------------------------------
   Collecting partial sequences stopped because of timeout
   ------------------------------------------------------------------------- *)

val anlrefpart = ref []
val maxparti = ref 0
val maxpart = 32
val ncoveri = ref 0
fun init_partial () = (anlrefpart := []; maxparti := 0; ncoveri := 0)

fun collect_partseq ot = 
  if !maxparti > maxpart then anlrefpart := [] else
  (
  case ot of
    Oleaf (an2,[]) => (incr maxparti; anlrefpart := an2 :: !anlrefpart)
  | Oleaf (an2,a2 :: m2) => (incr maxparti; anlrefpart := an2 :: !anlrefpart)
  | Odict (anl,d) =>
    ( 
    maxparti := !maxparti + length anl; 
    anlrefpart := anl @ !anlrefpart;
    app collect_partseq (map snd (dlist d))
    )
  )

(* -------------------------------------------------------------------------
   Checking if a program covers an OEIS sequence
   ------------------------------------------------------------------------- *)

val anlref = ref []

local open Arbint in

fun cover_oeis_aux f i ot = case ot of
    Oleaf (an2,[]) => anlref := an2 :: !anlref
  | Oleaf (an2,a2 :: m2) => 
    (
    case SOME (f i = a2) handle ProgTimeout => NONE of
      SOME true =>  
      (incr_timer (); incr ncoveri;
       cover_oeis_aux f (i + one) (Oleaf (an2,m2))) 
    | SOME false => ()
    | NONE => anlrefpart := [an2]
    )
  | Odict (anl,d) =>
    let val _ = anlref := anl @ !anlref in
      case SOME (f i) handle ProgTimeout => NONE of
        SOME a1 =>
        (
        case SOME (dfind a1 d) handle NotFound => NONE of 
          NONE => ()
        | SOME newot => (incr_timer (); incr ncoveri; 
                         cover_oeis_aux f (i + one) newot)
        )
      | NONE => app collect_partseq (map snd (dlist d))
    end

end (* local *)

fun cover_oeis_aux2 f = 
  let 
    val _ = (anlref := []; init_partial ())
    val _ = init_timer ();
    val _ = cover_oeis_aux f Arbint.zero otree;
    val t = Time.toReal (Timer.checkRealTimer (!rt_glob)) 
  in
    (!anlref, (!ncoveri, SOME t), !anlrefpart) 
  end

fun cover_oeis f = catch_perror cover_oeis_aux2 f 
  (fn () => (!anlref, (!ncoveri, NONE), !anlrefpart))

fun seqf_of p =
  let 
    val f = mk_exec p 
    fun g a = intpart (f (mk_rat a, rzero)) 
  in 
    g
  end
  
fun coverp_oeis p = cover_oeis (seqf_of p)
  
(* -------------------------------------------------------------------------
   Checking if a program covers a user-given sequence
   ------------------------------------------------------------------------- *)

local open Arbint in
fun cover_target_aux f i target = case target of 
    [] => (true, !ncoveri)
  | a :: m => if f i = a 
              then (incr_timer (); incr ncoveri; cover_target_aux f (i+one) m)
              else (false, !ncoveri)
end

fun cover_target_aux2 f target = 
  (
  ncoveri := 0;
  init_timer ();
  cover_target_aux f Arbint.zero target
  )

fun cover_target f target = catch_perror (cover_target_aux2 f) target 
  (fn () => (false, !ncoveri))

fun coverp_target p target = cover_target (seqf_of p) target

(* -------------------------------------------------------------------------
   Sequences generated by a program up to a number n.
   ------------------------------------------------------------------------- *)

fun penum p n = 
  let 
    val _ = init_slow_test ()
    val f = seqf_of p
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
    init_fast_test ();
    rev (!l)
  end
  

end (* struct *)

(* 
load "exec"; open exec; 
load "human"; open kernel human aiLib;
val p =  parse_human "(loop ( * 2 x) (+ x 2) 1)";
val p = parse_human "(+ (compr (% (- (loop ( * 2 x) (+ x 1) 1) 1) (+ x 2val (l1,t) = add_time (penum p) 5;)) x) 2"; 
humanf p;
val (l1,t) = add_time (penum p) 30;

*)
