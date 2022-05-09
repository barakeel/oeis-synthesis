structure bloom :> bloom =
struct

open HolKernel Abbrev boolLib aiLib kernel smlTimeout;
val ERR = mk_HOL_ERR "bloom";

(* OEIS array *)
val oraw = readl (selfdir ^ "/data/oeis");
val _ = print_endline ("oeis: " ^ its (length oraw));

val oseq = Array.tabulate (400000, fn _ => NONE);  

fun update_oseq s = 
  let 
    val aseq = String.tokens (fn x => x = #",") s
    val anum = (hd o String.tokens Char.isSpace o hd) aseq
    val an = string_to_int (tl_string anum) 
    val seq = map Arbint.fromString (tl aseq)
  in 
    Array.update (oseq, an, SOME seq)
  end 

val _ = app update_oseq oraw

(* Quotient tree *)
datatype stree = 
  Sleaf of prog * int list |
  Sdict of (int, stree) Redblackmap.dict

val sempty = Sdict (dempty Int.compare)

exception Sexists;

val scover = ref NONE

fun sadd (ptop,seq) st = case seq of 
  [] =>
  (
  case st of
    Sleaf (p,[]) =>
    if prog_compare_size (ptop,p) = LESS
    then (scover := SOME p; Sleaf (ptop,seq))
    else raise Sexists
  | Sleaf (_,a2 :: m2) => raise Sexists
  | Sdict d => 
    if dlength d = 0 then Sleaf (ptop,seq) else raise Sexists
  )
  | a1 :: m1 =>
  (
  case st of
    Sleaf (p,[]) => (scover := SOME p; Sleaf (ptop,seq)) 
     (*
     if prog_size ptop - prog_size p <= length seq + 1
     then (scover := SOME p; Sleaf (ptop,seq))
     else raise Sexists
     *)
  | Sleaf (p,a2 :: m2) => 
    sadd (ptop,seq) (Sdict (dnew Int.compare [(a2,Sleaf (p,m2))]))
  | Sdict d =>
    if dlength d = 0 then Sleaf (ptop,seq) else 
    let val vo = SOME (dfind a1 d) handle NotFound => NONE in
      case vo of 
        NONE => Sdict (dadd a1 (Sleaf (ptop,m1)) d)
      | SOME v => Sdict (dadd a1 (sadd (ptop,m1) v) d)
    end  
  )

fun snew x st = 
  let 
    val _ = scover := NONE
    val b = (ignore (sadd x st); true) handle Sexists => false
  in
    (b,!scover)
  end

(* OEIS tree *)
datatype ttree = 
  Tleaf of int * Arbint.int list |
  Tdict of int list * (Arbint.int, ttree) Redblackmap.dict

val tempty = Tdict ([],dempty Arbint.compare)

fun tadd (seq,an) st = case (st,seq) of
    (Tleaf (an2,[]),_) => 
    tadd (seq,an) (Tdict ([an2],dempty Arbint.compare))
  | (Tleaf (an2,a2 :: m2),_) => 
    tadd (seq,an) (Tdict ([], dnew Arbint.compare [(a2,(Tleaf (an2,m2)))]))
  | (Tdict (anl,d), []) => Tdict (an :: anl, d)
  | (Tdict (anl,d), a1 :: m1) =>
    let val sto = SOME (dfind a1 d) handle NotFound => NONE in
      case sto of 
        NONE => Tdict (anl, dadd a1 (Tleaf (an,m1)) d) 
      | SOME newst => Tdict (anl, dadd a1 (tadd (m1,an) newst) d)
    end

fun taddo (i,seqo,st) = 
  case seqo of NONE => st | SOME seq => tadd (seq,i) st

val ost = Array.foldli taddo tempty oseq


(* Cover *)
val anlref = ref []

local open Arbint in 

fun tcover_aux f i st = case st of
    Tleaf (an2,[]) => anlref := an2 :: !anlref
  | Tleaf (an2,a2 :: m2) => 
    if f (i,zero) = a2 then tcover_aux f (i + one) (Tleaf (an2,m2)) else ()
  | Tdict (anl,d) =>
    let 
      val _ = anlref := anl @ !anlref
      val a1 = f (i,zero)
      val sto = SOME (dfind a1 d) handle NotFound => NONE 
    in
      case sto of 
        NONE => ()
      | SOME newst => tcover_aux f (i + one) newst
    end

end

fun tcover f = 
  let val _ = anlref := [] in
    tcover_aux f Arbint.zero ost handle ProgTimeout => ();
    !anlref 
  end
  handle Div => []


fun infoq_int x = 
  if x = 0 then 1.0 
  else Math.ln (Real.abs (Real.fromInt x)) / (Math.ln 2.0)     

fun infoq_seq xl = sum_real (map infoq_int xl)


(* 
load "bloom"; open aiLib bloom;

val sl = tcover (List.concat (List.tabulate (64, fn _ => [0,1]))) ost;


val sl = tcover [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53] ost;
val sl = tcover [0,1,1,2,3,5,8,13,21,34,55,89,89+55,2*89+55,3*89+2*55,5*89+3*55] st;

fun sadd_nomem seq st = if snew seq st then st else sadd seq st;
snew [1,2,3] st;

(case st of Sdict d => dkeys d);
*)




(*
fun repeatn n f = 
  if n <= 0 then () else (f (); repeatn (n-1) f);
val size = 1024;
val d = dset Int.compare (List.tabulate (size,I));
fun f1 () = dfind (size - 1) d;
val l = List.tabulate (size,(fn i => (i,())));
fun f2 () = assoc (size - 1) l;
time (repeatn 10000000) f1;
time (repeatn 10000000) f2
*)

end (* struct *)











