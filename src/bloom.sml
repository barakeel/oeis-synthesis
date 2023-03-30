structure bloom :> bloom =
struct

open HolKernel Abbrev boolLib aiLib kernel;
val ERR = mk_HOL_ERR "bloom";
type anum = int

local open IntInf in
  val azero = fromInt 0
  val aone = fromInt 1
  fun aincr x = x + aone
  fun adecr x = x - aone
end 

(* -------------------------------------------------------------------------
   Findstat data read from disk
   ------------------------------------------------------------------------- *)

fun enum_perm l = case l of 
    []  => raise ERR "enum_perm" "empty" 
  | [a] => [[a]]
  | _   => List.concat 
    (map (fn x => enum_perm_one x (filter (fn y => y <> x) l)) l)

and enum_perm_one a l = map (fn x => a :: x) (enum_perm l);

val perml = List.concat (
List.tabulate (7, fn x =>  enum_perm (List.tabulate (x+1,I))));
val permlength = length perml
val permd = dnew (list_compare Int.compare) (number_snd 0 perml)
val permv = Vector.fromList perml


(* 
val perminput40 =
random_subset 10 (enum_perm (List.tabulate (4,I))) @
random_subset 10 (enum_perm (List.tabulate (5,I))) @
random_subset 10 (enum_perm (List.tabulate (6,I))) @
random_subset 10 (enum_perm (List.tabulate (7,I)));
*)
val perminput40  =  
   [[0, 3, 1, 2], [3, 2, 0, 1], [3, 0, 1, 2], [1, 3, 0, 2], [2, 1, 3, 0],
    [0, 1, 2, 3], [2, 0, 3, 1], [1, 0, 3, 2], [3, 1, 0, 2], [2, 1, 0, 3],
    [3, 1, 0, 2, 4], [3, 1, 4, 2, 0], [4, 2, 0, 3, 1], [2, 0, 3, 4, 1],
    [4, 2, 3, 1, 0], [0, 2, 1, 3, 4], [3, 0, 2, 1, 4], [1, 4, 0, 3, 2],
    [4, 3, 1, 2, 0], [4, 3, 0, 2, 1], [3, 0, 1, 2, 4, 5], [0, 4, 2, 3, 5, 1],
    [5, 3, 0, 1, 4, 2], [5, 2, 1, 4, 3, 0], [1, 5, 0, 2, 3, 4],
    [4, 0, 5, 1, 2, 3], [2, 4, 1, 0, 5, 3], [4, 3, 2, 0, 1, 5],
    [1, 5, 2, 4, 3, 0], [0, 2, 3, 4, 5, 1], [1, 4, 5, 2, 0, 3, 6],
    [4, 1, 6, 0, 2, 3, 5], [5, 3, 4, 2, 1, 6, 0], [2, 4, 5, 1, 3, 6, 0],
    [6, 0, 1, 2, 3, 4, 5], [6, 0, 4, 2, 1, 5, 3], [2, 4, 0, 6, 5, 1, 3],
    [3, 2, 1, 6, 5, 0, 4], [5, 2, 3, 1, 0, 4, 6], [6, 2, 1, 3, 0, 4, 5]];

val perminputl = tl (first_n 9 perml) @ perminput40;
val perminputv = Vector.fromList perminputl


local open json in

fun is_sep c = mem c [#",",#"[",#"]"]
fun to_intl x = map ((fn x => x - 1) o string_to_int) (String.tokens is_sep x)

fun rm_ok y = case y of OK x => x | _ => raise ERR "rm_ok" ""
fun get_maps json = case json of 
    OBJECT (("included",b) :: m) => get_maps b
  | OBJECT [("Maps",b)] => get_maps b
  | OBJECT l => l
  | _ => raise ERR "get_maps" "";
fun get_io_one json = case json of
    ARRAY [STRING s1, STRING s2] => (s1,s2)
  | _ => raise ERR "get_io_one" ""
fun get_io json =  case json of 
    OBJECT [("Values",ARRAY jsonl)] => 
      let 
        val (al,bl) = split (map get_io_one (first_n permlength jsonl)) 
        val (al1,bl1) = (map to_intl al, map to_intl bl)   
      in
        if al1 <> perml then raise ERR "get_io" "" else
        Vector.fromList (map (fn x => dfind x permd) bl1)
      end
  | _ => raise ERR "get_io" ""

val fsmap = 
  if !fs_flag then
  let
    val fsraw = hd (readl (selfdir ^ "/data/findstat_maps"))
    val json0 = parse fsraw
    val json1 = rm_ok json0
    val json2 = get_maps json1
    val json3 = filter (fn x => fst x <> "Mp00252") json2
    val json4 = map_snd get_io json3
  in
    json4
  end
  else []


val mapl = map fst fsmap

fun apply_map s perml = 
  let val v = assoc s fsmap in map (fn x => (Vector.sub(v,x))) perml end

fun apply_mapl sl perml = case sl of [] => perml | s :: m =>
  apply_mapl m (apply_map s perml); 

end

(* load "bloom"; open bloom aiLib; *)

(* -------------------------------------------------------------------------
   OEIS array read from disk
   ------------------------------------------------------------------------- *)

val oraw = 
  if !fs_flag 
  then [] else 
    let val r = readl (selfdir ^ "/data/oeis") in
      print_endline ("oeis: " ^ its (length r)); r
    end

(* val solved = enew Int.compare 
  (map fst (read_iprogl (selfdir ^ "/model/isol_online"))); *)
val oseq = 
  if !fs_flag 
  then Array.tabulate (30000, fn _ => NONE)
  else Array.tabulate (400000, fn _ => NONE)

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

val mapcompl = if not (!fs_flag) then [] else
  let fun f x = cartesian_productl (List.tabulate (x + 1, fn _ => mapl)) in
    List.concat (List.tabulate (3,f)) 
  end
val permil = map (fn x => dfind x permd) perminputl
val fs1 = map_assoc (fn x => apply_mapl x permil) mapcompl;
val fs2 = mk_sameorder_set (snd_compare (list_compare Int.compare)) fs1;
val compd = dnew (list_compare String.compare) (number_snd 0 (map fst fs2));
val compv = Vector.fromList (map fst fs2)
val fsraw = map_fst (fn x => dfind x compd) fs2

fun fs_update_oseq (an,seq) = 
  Array.update (oseq, an, SOME (map IntInf.fromInt seq)) 

val _ = 
  if !fs_flag 
  then app fs_update_oseq fsraw
  else app update_oseq oraw

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
  | (Oleaf (an2, a2 :: m2),_) => 
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

datatype otreen = 
  Oleafn of anum * IntInf.int list |
  Odictn of anum list * (IntInf.int * otreen) list

fun rm_dict ot = case ot of
    Oleaf x => Oleafn x
  | Odict (anl,d) => Odictn (anl, map_snd rm_dict (dlist d))

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
