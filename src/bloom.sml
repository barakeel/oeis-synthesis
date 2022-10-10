structure bloom :> bloom =
struct

open HolKernel Abbrev boolLib aiLib kernel smlTimeout;
val ERR = mk_HOL_ERR "bloom";
type anum = int

local open IntInf in
  val azero = fromInt 0
  val aone = fromInt 1
  fun aincr x = x + aone
  fun adecr x = x - aone
end 

(* -------------------------------------------------------------------------
   OEIS array read from disk
   ------------------------------------------------------------------------- *)

val oraw = readl (selfdir ^ "/data/oeis");
val _ = print_endline ("oeis: " ^ its (length oraw));
(* val solved = enew Int.compare 
  (map fst (read_iprogl (selfdir ^ "/model/isol_online"))); *)
val oseq = Array.tabulate (400000, fn _ => NONE);  

fun update_oseq s = 
  let 
    val aseq = String.tokens (fn x => x = #",") s
    val anum = (hd o String.tokens Char.isSpace o hd) aseq
    val an = string_to_int (tl_string anum) 
    val seq = map (valOf o IntInf.fromString) (tl aseq)
  in 
    (*  if an > 1 then () else
        if emem an solved then () else *)
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
  Oleaf of anum * IntInf.int list |
  Odict of anum list * (IntInf.int, otree) Redblackmap.dict

val oempty = Odict ([], dempty IntInf.compare)

fun oadd (seq,an) ot = case (ot,seq) of
    (Oleaf (an2,[]),_) => 
    oadd (seq,an) (Odict ([an2],dempty IntInf.compare))
  | (Oleaf (an2,a2 :: m2),_) => 
    oadd (seq,an) (Odict ([], dnew IntInf.compare [(a2,(Oleaf (an2,m2)))]))
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

fun cover_oeis_aux f i ot = case ot of
    Oleaf (an2,[]) => anlref := (an2,!abstimer) :: !anlref
  | Oleaf (an2,a2 :: m2) => 
    (
    case SOME (f i = a2) handle ProgTimeout => NONE of
      SOME true =>  
      (incr_timer (); incr ncoveri;
       cover_oeis_aux f (aincr i) (Oleaf (an2,m2))) 
    | SOME false => ()
    | NONE => anlrefpart := [an2]
    )
  | Odict (anl,d) =>
    let val _ = anlref := map (fn x => (x,!abstimer)) anl @ !anlref in
      case SOME (f i) handle ProgTimeout => NONE of
        SOME a1 =>
        (
        case SOME (dfind a1 d) handle NotFound => NONE of 
          NONE => ()
        | SOME newot => (incr_timer (); incr ncoveri; 
                         cover_oeis_aux f (aincr i) newot)
        )
      | NONE => app collect_partseq (map snd (dlist d))
    end

fun cover_oeis_aux2 f = 
  let 
    val _ = (anlref := []; init_partial ())
    val _ = init_timer ();
    val _ = cover_oeis_aux f azero otree
  in
    (!anlref, !ncoveri, !anlrefpart) 
  end

fun cover_oeis f = catch_perror cover_oeis_aux2 f 
  (fn () => (!anlref, !ncoveri, !anlrefpart))

(* -------------------------------------------------------------------------
   Checking if a program covers a user-given sequence
   ------------------------------------------------------------------------- *)

fun cover_target_aux f i target = case target of 
    [] => (true, !ncoveri)
  | a :: m => 
    if f i = a 
    then (incr_timer (); incr ncoveri; cover_target_aux f (aincr i) m)
    else (false, !ncoveri)

fun cover_target_aux2 f target = 
  (
  ncoveri := 0;
  init_timer ();
  cover_target_aux f azero target
  )

fun cover_target f target = catch_perror (cover_target_aux2 f) target 
  (fn () => (false, !ncoveri))
  
(* -------------------------------------------------------------------------
   Select a random OEIS sequence
   ------------------------------------------------------------------------- *)

fun select_random_target () =
  let
    fun loop () =
      let val i = random_int (0, Array.length oseq - 1) in
        case Array.sub (oseq, i) of NONE => loop () | SOME seq => (seq,i)
      end
    val (targetseq,seqname) = loop ()
    val _ = target_glob := targetseq
    val _ = print_endline 
      ("target " ^ its seqname ^ ": " ^ string_of_seq (!target_glob))
  in
    ()
  end


end (* struct *)
