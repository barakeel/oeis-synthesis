(* ========================================================================= *)
(* DESCRIPTION   : Find non-overlapping subsequences (strings)               *)
(* ========================================================================= *)

structure trie :> trie =
struct

open HolKernel aiLib kernel
val ERR = mk_HOL_ERR "trie"

val maxdefsize = 2
val minscore = 1
val offset = 16

datatype trie = 
  Trie of int ref * int ref * (int,trie) Redblackmap.dict ref;

fun emptyTrie () = Trie (ref 0, ref 0, ref (dempty Int.compare));

val rm_flag = ref false
val dirtyl = ref []
fun clean () = (app (fn x => x := 0) (!dirtyl); dirtyl := [])

fun tadd_aux (startpos,curpos) l (Trie (count, pos, children)) =
  (
  if startpos >= !pos 
  then (if !rm_flag then decr count else incr count; 
        pos := curpos;
        dirtyl := pos :: (!dirtyl))
  else ()
  ;
  (
  case l of [] => () | tok :: rest =>
  let
    val child = case dfindo tok (!children) of
      SOME t => t
    | NONE =>
      let val t = emptyTrie () in
        children := dadd tok t (!children); t
      end
  in
    tadd_aux (startpos, curpos + 1) rest child
  end
  )
  );

fun tadd startpos l d = tadd_aux (startpos,startpos) (first_n maxdefsize l) d

fun taddl_aux d startpos l = case l of [] => () | a :: m =>
  (tadd startpos l d; taddl_aux d (startpos + 1) m);

fun taddl d l = let val r = taddl_aux d 0 l in clean (); r end

fun treml d l = (rm_flag := true; taddl d l; rm_flag := false) 

fun tnew l = let val d = emptyTrie () in app (taddl d) l; d end;

fun tlist threshold t =
  let
    val out = ref []
    fun aux (Trie (count, _, children)) (path,n) =
      (
      let val sc = !count * (n-1) in
        if sc > threshold
        then out := (rev path, sc) :: !out 
        else ()
      end
      ;
      dapp (fn (tok, child) => aux child (tok::path,n+1)) (!children)
      )
  in
    aux t ([],0); !out
  end;

(* -------------------------------------------------------------------------
   Find the most compressing def, and replace it in the trie
   ------------------------------------------------------------------------- *)

fun tmax t =
  let
    val maxsc = ref 0
    val maxpath = ref []
    fun aux (Trie (count, _, children)) (path,n) =
      (
      let val sc = !count * (n-1) in
        if sc > !maxsc then (maxsc := sc; maxpath := rev path) else ()
      end
      ;
      dapp (fn (tok, child) => aux child (tok::path,n+1)) (!children)
      )
  in
    aux t ([],0); (!maxpath,!maxsc)
  end;

fun is_prefix_cont def p = case (def,p) of 
      ([],cont) => SOME cont
    | (_,[]) => NONE 
    | (a1 :: m1, a2 :: m2) => if a1 <> a2 then NONE else is_prefix_cont m1 m2
   
fun name_def_aux changed (def,defn) p = case p of 
    [] => []
  | a :: m =>
  (
  case is_prefix_cont def p of
    NONE => a :: name_def_aux changed (def,defn) m
  | SOME cont => (changed := true; defn :: name_def_aux changed (def,defn) cont)
  )

fun name_def d (def,defn) p = 
  let 
    val changed = ref false
    val newp = name_def_aux changed (def,defn) p
  in
    if not (!changed) then p else (treml d p; taddl d newp; newp) 
  end

fun mk_def_aux (curtot,tot) d defn maxdef (defl,pl) =
  if defn >= offset + maxdef then (defl,pl) else
  let val ((def,sc),t1) = add_time tmax d in
    if sc < minscore then (defl,pl) else
    let 
      val (newpl,t2) = add_time (map (name_def d (def,defn))) pl 
      val newdefl = (def,defn) :: defl
      val newcurtot = curtot - sc
      val _ = print_endline (its defn ^ ": " ^ ilts def ^ ", " ^ its sc ^ ", " ^
        rts_round 4 (int_div newcurtot tot) ^ ", " ^ rts_round 4 (t1+t2))
      (*
      val test = sum_int (map length newpl)
      val _ = if test <> newcurtot 
              then raise ERR "mk_def_aux" (its test ^ " " ^ its newcurtot)
              else ()
       *)
    in
      mk_def_aux (newcurtot,tot) d (defn + 1) maxdef (newdefl,newpl)
    end
  end;

fun mk_def d maxdef pl = 
  let val i = sum_int (map length pl) in
    print_endline ("total size: " ^ its i);
    mk_def_aux (i,i) d offset maxdef ([],pl)
  end

(* 
load "trie"; open aiLib kernel trie;

val sol = read_itprogl (selfdir ^ "/model/itsol209");
val pll = map (fn (_,tpl) => map (tokenl_of_prog o snd) tpl) sol;
val pl = List.concat pll;
val (trie,t) = add_time tnew pl;
val ((defl,newpl),t) = add_time (mk_def trie 100) pl;
val distrib1 = dlist (count_dict (dempty Int.compare) (map length newpl));
val i2 = sum_int (map length newpl);

PolyML.print_depth 200;
val distrib0 = dlist (count_dict (dempty Int.compare) (map length pl));


val i1 = sum_int (map length pl);



val defn = 16; 
val pl' = map (name_def (def,defn)) pl;


*)




end (* struct *)
