structure bloom :> bloom =
struct

open HolKernel Abbrev boolLib aiLib kernel smlTimeout;
val ERR = mk_HOL_ERR "bloom";
type anum = int

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

datatype otree = 
  Oleaf of anum * Arbint.int list |
  Odict of anum list * (Arbint.int, otree) Redblackmap.dict

val oempty = Odict ([], dempty Arbint.compare)

fun oadd (seq,an) ot = case (ot,seq) of
    (Oleaf (an2,[]),_) => 
    oadd (seq,an) (Odict ([an2],dempty Arbint.compare))
  | (Oleaf (an2,a2 :: m2),_) => 
    oadd (seq,an) (Odict ([], dnew Arbint.compare [(a2,(Oleaf (an2,m2)))]))
  | (Odict (anl,d), []) => Odict (an :: anl, d)
  | (Odict (anl,d), a1 :: m1) =>
    let val oto = SOME (dfind a1 d) handle NotFound => NONE in
      case oto of 
        NONE => Odict (anl, dadd a1 (Oleaf (an,m1)) d) 
      | SOME newot => Odict (anl, dadd a1 (oadd (m1,an) newot) d)
    end

fun oaddo (i,seqo,ot) = 
  case seqo of NONE => ot | SOME seq => oadd (seq,i) ot

val otree = Array.foldli oaddo oempty oseq


  

end (* struct *)
