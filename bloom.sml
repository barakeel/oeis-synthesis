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
        val seq0 = first_n (!maxinput) (tl aseq)
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

val bmod = 4093082899
val bmodw = Word.fromInt bmod
val zerow = Word.fromInt 0

val mal =
   [(1507141,3349037),
    (8089339,5119783),
    (3971411,1086413),
    (2637251,7101337),
    (5695777,5695777),
    (7774433,6630097),
    (6048967,4814759)]

val malw = first_n 4
  (map (fn (a,b) => (Word.fromInt a, Word.fromInt b)) mal)

fun hash_seq (multer,adder) l =
  let
    open Word
    fun loop acc l' = case l' of
       [] => toInt (acc mod bmodw)
     | a :: m => loop ((acc + fromInt a) * multer + adder) m
  in
    loop zerow l
  end

fun bmem seq b =
  let fun g ma = BoolArray.sub (b,hash_seq ma seq) in
    all g malw
  end

fun badd seq b =
  let fun f ma = BoolArray.update (b,hash_seq ma seq,true) in
    app f malw
  end


fun bmem_pi pi b =
  let fun g ma = BoolArray.sub (b,hash_seq ma (pi_to_hseq pi)) in
    all g malw
  end

fun badd_pi pi b =
  let fun f ma = BoolArray.update (b,hash_seq ma (pi_to_hseq pi),true) in
    app f malw
  end

fun pi_to_hl pi = 
  let val hseq = pi_to_hseq pi in
     map (fn x => hash_seq x hseq) malw
   end

fun bmem_hl hl b =
  let fun g x = BoolArray.sub (b,x) in
    all g hl
  end

fun badd_hl hl b =
  let fun f x = BoolArray.update (b,x,true) in
    app f hl
  end

fun badd_check seq b =
  let fun f ma = BoolArray.update (b,hash_seq ma seq,true) in
    if bmem seq b then print_endline (string_of_seq seq) else ();
    app f malw
  end

val (odv,odname) = 
  let
    val l = import_oseq () 
    val odvref = Vector.tabulate (!maxinput + 1, 
      fn _ => ref (eempty seq_compare))
    fun f seq = 
      let val odref = Vector.sub (odvref,length seq) in
        odref := eadd seq (!odref)
      end  
    val _ = app f (map fst l)
    val r = Vector.map ! odvref
    val odname_aux = dregroup seq_compare l
  in
    print_endline ("selected: " ^ its (dlength odname_aux));
    (r, odname_aux)
  end

fun find_wins p sem =
  if depend_on_i p then [] else
  let
    val seql = List.tabulate (!maxinput + 1, fn i => 
      let val subseq = first_n i sem in
        if emem subseq (Vector.sub (odv,i))
        then SOME subseq
        else NONE
      end)
  in
    List.mapPartial I seql
  end 


(* load "bloom"; open aiLib bloom;
  val (l,d) = import_arbseq (); 
  dlength d;
 *)


end (* struct *)











