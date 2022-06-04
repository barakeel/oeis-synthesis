structure jump :> jump =
struct

open HolKernel Abbrev boolLib aiLib kernel;
val ERR = mk_HOL_ERR "jump";

(* construct the jump tree *)
datatype jtree = 
  Jleaf of int list |
  Jdict of (bool * (int, jtree) Redblackmap.dict)

(* split if bool + dlength >= 2 *)

val jempty = Jdict (false, dempty Int.compare)

fun jadd actl1 jt = case (jt,actl1) of
    (Jleaf [], _) => jadd actl1 (Jdict (true, dempty Int.compare))
  | (Jleaf (a2 :: m2),_) => 
    jadd actl1 (Jdict (false, dnew Int.compare [(a2,Jleaf m2)]))
  | (Jdict (b,d), []) => Jdict (true, d)
  | (Jdict (b,d), a1 :: m1) =>
    case dfindo a1 d of 
      NONE => Jdict (b, dadd a1 (Jleaf m1) d) 
    | SOME jtchild => Jdict (b, dadd a1 (jadd m1 jtchild) d)


end (* struct *)

(* -------------------------------------------------------------------------
   Test jump
   ------------------------------------------------------------------------- 

load "jump"; open aiLib human execarb rl qsynt;
time_opt := SOME 60.0;

*)



