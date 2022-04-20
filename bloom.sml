structure bloom :> bloom =
struct

open HolKernel Abbrev boolLib aiLib kernel;
val ERR = mk_HOL_ERR "bloom";

fun string_to_int_err s = string_to_int s handle Overflow => error

fun import_oseq () =
  let 
    val sl = readl (selfdir ^ "/data/oeis");
    val _ = print_endline ("oeis: " ^ its (length sl))
    fun f s =
      let 
        val aseq = (String.tokens (fn x => x = #",") s)
        val anum = (hd o String.tokens Char.isSpace o hd) aseq
        val seq0 = first_n maxinput (tl aseq)
      in 
        (map string_to_int_err seq0, anum)
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
        val seq1 = map Arbint.fromString (tl aseq)
      in 
         (seq1,anum)
      end
    val r1 = map f sl
    val r2 = dregroup (list_compare Arbint.compare) r1
    val _ = print_endline (its (dlength r2))
  in
    (r1,r2)
  end

fun import_arbseq_fst () =
  let 
    val sl = readl (selfdir ^ "/data/oeis");
    val _ = print_endline ("oeis: " ^ its (length sl))
    fun f s =
      let 
        val aseq = (String.tokens (fn x => x = #",") s)
        val anum = (hd o String.tokens Char.isSpace o hd) aseq
        val seq1 = map Arbint.fromString (tl aseq)
      in 
         (seq1,anum)
      end
  in
    map f sl
  end

val odv_glob = ref (Vector.fromList [])
val odname_glob = ref (dempty seq_compare)

fun init_od () =
  let
    val l = import_oseq () 
    val odvref = Vector.tabulate (maxinput + 1, 
      fn _ => ref (eempty seq_compare))
    fun f seq = 
      let val odref = Vector.sub (odvref,length seq) in
        odref := eadd seq (!odref)
      end  
    val _ = app f (map fst l)
    val odname_aux = dregroup seq_compare l
  in
    print_endline ("selected: " ^ its (dlength odname_aux));
    odname_glob := odname_aux;
    odv_glob := Vector.map ! odvref
  end

fun find_wins p sem =
  (* if depend_on_y p then [] else *)
  let
    val seql = List.tabulate (maxinput + 1, fn i => 
      let val subseq = first_n i sem in
        if emem subseq (Vector.sub (!odv_glob,i))
        then SOME subseq
        else NONE
      end)
  in
    List.mapPartial I seql
  end 

datatype stree = 
  Sleaf of int list |
  Sdict of (int, stree) Redblackmap.dict
;

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
    end;

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


(* 
load "bloom"; open aiLib bloom;

PolyML.print_depth 2;
val l0 = time (import_oseq) ();
val l1 = time (map fst) l0;
PolyML.print_depth 40;

val st = time (foldl (uncurry tadd) tempty) l0;

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











