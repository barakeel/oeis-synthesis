structure bloom :> bloom =
struct

open HolKernel Abbrev boolLib aiLib kernel smlTimeout;
val ERR = mk_HOL_ERR "bloom";

(* -------------------------------------------------------------------------
   OEIS array read from disk
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   OEIS tree
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   Checking if a program covers an OEIS sequence
   ------------------------------------------------------------------------- *)

val anlref = ref []
val timeincr = 0.00005
fun incr_timer () = timelimit := !timelimit + timeincr

local open Arbint in

fun tcover_aux f i st = case st of
    Tleaf (an2,[]) => anlref := an2 :: !anlref
  | Tleaf (an2,a2 :: m2) => 
    if f (i,zero) = a2 
    then 
      (incr_timer ();
       tcover_aux f (i + one) (Tleaf (an2,m2))) 
    else ()
  | Tdict (anl,d) =>
    let 
      val _ = anlref := anl @ !anlref
      val a1 = f (i,zero)
      val sto = SOME (dfind a1 d) handle NotFound => NONE 
    in
      case sto of 
        NONE => ()
      | SOME newst => (incr_timer (); tcover_aux f (i + one) newst)
    end

end (* local *)

fun tcover f = 
  let val _ = anlref := [] in
    timelimit := timeincr;
    tcover_aux f Arbint.zero ost;
    !anlref
  end
  handle Div => !anlref | ProgTimeout => !anlref

(* -------------------------------------------------------------------------
   Checking if a program covers a user-given sequence
   ------------------------------------------------------------------------- *)

local open Arbint in
fun fcover_aux f i target = case target of 
    [] => true
  | a :: m => if f (i,zero) = a 
              then (incr_timer (); fcover_aux f (i+one) m)
              else false
end

fun fcover f target = 
  (
  timelimit := timeincr;
  fcover_aux f Arbint.zero target
  )
  handle Div => false | ProgTimeout => false

end (* struct *)
