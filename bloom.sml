structure bloom :> bloom =
struct

open HolKernel Abbrev boolLib aiLib kernel;
val ERR = mk_HOL_ERR "bloom";

fun map_err acc f l = case l of 
    [] => rev acc
  | a :: m => 
    let val x = f a handle Overflow => valOf Int.maxInt in
      map_err (x :: acc) f m
    end

fun import_oseq () =
  let 
    val sl = readl (selfdir ^ "/data/oeis");
    val _ = print_endline ("oeis: " ^ its (length sl))
    fun f s =
      let 
        val aseq = (String.tokens (fn x => x = #",") s)
        val anum = (hd o String.tokens Char.isSpace o hd) aseq
        val seq = map_err [] string_to_int (tl aseq)
      in 
        (seq, anum)
      end
  in
    map f sl
  end

fun import_arbseq () =
  let 
    val sl = readl (selfdir ^ "/data/oeis");
    val _ = print_endline ("oeis: " ^ its (length sl))
    fun f s =
      let 
        val aseq = (String.tokens (fn x => x = #",") s)
        val anum = (hd o String.tokens Char.isSpace o hd) aseq
        val seq = map Arbint.fromString (tl aseq)
      in 
        (seq,anum)
      end
  in
    map f sl
  end


datatype stree = 
  Sleaf of int list |
  Sdict of (int, stree) Redblackmap.dict

val sempty = Sdict (dempty Int.compare)

fun sadd seq st = case seq of [] => st | a1 :: m1 => 
  (
  case st of
    Sleaf [] => Sleaf seq  
  | Sleaf (a2 :: m2) => 
    sadd seq (Sdict (dnew Int.compare [(a2,Sleaf m2)]))
  | Sdict d => 
    let val vo = SOME (dfind a1 d) handle NotFound => NONE in
      case vo of 
        NONE => Sdict (dadd a1 (Sleaf m1) d)
      | SOME v => Sdict (dadd a1 (sadd m1 v) d)
    end  
  )

fun smem seq st = case seq of 
    [] =>
    (
    case st of
      Sleaf [] => (true,true)
    | Sleaf _ => (true,false)
    | Sdict d => if dlength d = 0 then (true,true) else (true,false)
    )
  | a1 :: m1 => 
    (
    case st of
      Sleaf [] => (false,false)
    | Sleaf (a2 :: m2) => 
      if not (a1 = a2) then (false,false) else smem m1 (Sleaf m2)
    | Sdict d => 
      let val vo = SOME (dfind a1 d) handle NotFound => NONE in
        case vo of 
          NONE => (false,false)
        | SOME v => smem m1 v
      end  
    )

datatype ttree = 
  Tleaf of string * seq |
  Tdict of string list * string list * (int, ttree) Redblackmap.dict;

val tempty = Tdict ([],[],dempty Int.compare)

fun tadd (seq,s1) st = case (st,seq) of
    (Tleaf (s2,[]),_) => 
    tadd (seq,s1) (Tdict ([s2], [s2], dempty Int.compare))
  | (Tleaf (s2,a2 :: m2),_) => 
    tadd (seq,s1) (Tdict ([s2], [], dnew Int.compare [(a2,(Tleaf (s2,m2)))]))
  | (Tdict (sl,slfin,d), []) => Tdict (s1 :: sl, s1 :: slfin, d)
  | (Tdict (sl,slfin,d), a1 :: m1) =>
    let val vo = SOME (dfind a1 d) handle NotFound => NONE in
      case vo of 
        NONE => Tdict (s1 :: sl, slfin, dadd a1 (Tleaf (s1,m1)) d) 
      | SOME v => Tdict (s1 :: sl, slfin, dadd a1 (tadd (m1,s1) v) d)
    end

fun tcover seq st = case (st,seq) of
    (Tleaf (s2,[]),_) => [s2]
  | (Tleaf (s2,seq2),_) => if seq = seq2 then [s2] else []
  | (Tdict (sl,slfin,d), []) => sl
  | (Tdict (sl,slfin,d), a1 :: m1) =>
    let val vo = SOME (dfind a1 d) handle NotFound => NONE in
      case vo of 
        NONE => sl
      | SOME v => slfin @ tcover m1 v
    end;

val oseq = import_oseq ()
val ost = foldl (uncurry tadd) tempty oseq

fun infoq_int x = 
  if x = 0 then 1.0 
  else Math.ln (Real.abs (Real.fromInt x)) / (Math.ln 2.0)     

fun infoq_seq xl = sum_real (map infoq_int xl)

fun find_wins sem = 
  if infoq_seq sem < 64.0 then [] else tcover sem ost


(* 
load "bloom"; open aiLib bloom;

PolyML.print_depth 2;
val l0 = time (import_oseq) ();
val l1 = time (map fst) l0;
PolyML.print_depth 40;



val sl = tcover [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53] st;
val sl = tcover [0,1,1,2,3,5,8,13,21,34,55,89,89+55,2*89+55,3*89+2*55,5*89+3*55] st;














fun sadd_nomem seq st = if smem seq st then st else sadd seq st;








smem [1,2,3] st;

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











