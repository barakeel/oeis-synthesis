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

val oseql = 
  let fun f (i,x,l) = case x of NONE => l | SOME y => (i,y) :: l in
    Array.foldri f [] oseq
  end

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
   Collecting partial sequences stopped because of timeout
   ------------------------------------------------------------------------- *)

val anlrefpart = ref []
val maxparti = ref 0
val maxpart = 32
val ncoveri = ref 0
fun init_partial () = (anlrefpart := []; maxparti := 0; ncoveri := 0)

fun collect_partseq st = 
  if !maxparti > maxpart then anlrefpart := [] else
  (
  case st of
    Tleaf (an2,[]) => (incr maxparti; anlrefpart := an2 :: !anlrefpart)
  | Tleaf (an2,a2 :: m2) => (incr maxparti; anlrefpart := an2 :: !anlrefpart)
  | Tdict (anl,d) =>
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

fun cover_oeis_aux f i st = case st of
    Tleaf (an2,[]) => anlref := an2 :: !anlref
  | Tleaf (an2,a2 :: m2) => 
    (
    case SOME (f (i,zero) = a2) handle ProgTimeout => NONE of
      SOME true =>  
      (incr_timer (); incr ncoveri;
       cover_oeis_aux f (i + one) (Tleaf (an2,m2))) 
    | SOME false => ()
    | NONE => anlrefpart := [an2]
    )
  | Tdict (anl,d) =>
    let val _ = anlref := anl @ !anlref in
      case SOME (f (i,zero)) handle ProgTimeout => NONE of
        SOME a1 =>
        (
        case SOME (dfind a1 d) handle NotFound => NONE of 
          NONE => ()
        | SOME newst => (incr_timer (); incr ncoveri; 
                         cover_oeis_aux f (i + one) newst)
        )
      | NONE => app collect_partseq (map snd (dlist d))
    end

end (* local *)

fun cover_oeis f = 
  let val _ = (anlref := []; init_partial ()) in
    init_timer ();
    cover_oeis_aux f Arbint.zero ost;
    (!anlref, !ncoveri, !anlrefpart) 
  end
  handle Div => (!anlref, !ncoveri, !anlrefpart) 
       | ProgTimeout => (!anlref, !ncoveri, !anlrefpart)

(* -------------------------------------------------------------------------
   Checking if a program covers a user-given sequence
   ------------------------------------------------------------------------- *)

local open Arbint in
fun cover_target_aux f i target = case target of 
    [] => true
  | a :: m => if f (i,zero) = a 
              then (incr_timer (); cover_target_aux f (i+one) m)
              else false
end

fun cover_target f target = 
  (
  init_timer ();
  cover_target_aux f Arbint.zero target
  )
  handle Div => false | ProgTimeout => false

end (* struct *)
