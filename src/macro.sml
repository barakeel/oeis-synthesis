structure macro :> macro =
struct

open HolKernel Abbrev boolLib aiLib kernel

val ERR = mk_HOL_ERR "macro"
type macro = int list

val hashop = Vector.length operv
val minop = hashop + 1
val maxop = hashop + 10

(* write random macro *)
fun random_macro x = List.tabulate (x, fn _ => random_int (0,maxop));

(* remove unaccessible macros *)
fun rm_undef (macro,i) = filter (fn x => x < minop + i) macro;

(* storing expanded macro in a vector *)
val empty_macrov: int list vector = Vector.tabulate (10, fn _ => []);
val macrov = ref empty_macrov; 
fun is_macro x = x >= minop; 
fun index_macro x = x - minop;

(* expand macro *)
fun expand_aux acc munit = case munit of
    [] => rev acc
  | (a,n) :: m => 
    if not (is_macro a) then expand_aux ((a,n) :: acc) m else 
    let val mrefn = map (fn x => (x,n)) 
      (rev (Vector.sub (!macrov, index_macro a))) 
    in
      expand_aux (mrefn @ acc) m
    end

fun expand macro = expand_aux [] (number_snd 0 macro);

fun expandi (macro,i) =
  let val macroi = expand macro in
    if i >= 10 orelse length macroi > 1000 then () else 
    macrov := Vector.update (!macrov,i, map fst macroi);
    macroi
  end;
  
(* collect programs from a macro in a context *)
fun next_board (board : (prog * int * int) list) (move,moven) =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 <> arity  (* ignore errors *)
    then board
    else (Ins (move, rev (map #1 l1)), 
          list_imin (moven :: map #2 l1), moven) :: l2
  end;

fun collect_prog moveltop = 
  let 
    val progl = ref []
    fun loop board movel = case movel of [] => () | (move,moven) :: m => 
      let 
        val newboard = next_board board (move,moven)
        val _ = if null newboard then () else progl := hd newboard :: !progl
      in
        loop newboard m
      end
   in
     loop [] moveltop;
     !progl
   end;

fun subseq (n,m) l = first_n (m-n+1) (snd (part_n n l));

fun lconcatw_aux x ll = case ll of
    [] => []
  | [a] => [a]
  | a :: m => a :: [x] :: lconcatw_aux x m;
 
fun lconcatw x ll = List.concat (lconcatw_aux x ll);

fun collect_prog_standalone macro =
  let 
    val _ = macrov := empty_macrov
    val macrol1 = rpt_split_sl hashop macro;
    val macrol2 = map rm_undef (number_snd 0 macrol1)
    val sizev = Vector.fromList (map length macrol2)
    fun size_of i = Vector.sub (sizev, index_macro i)
    fun f l = mk_fast_set Int.compare (filter is_macro l)
    val depv = Vector.fromList (map f macrol2);
    fun dep_of i = Vector.sub (depv,index_macro i);
    fun depsize_of carved =
      let 
        val depl1 = mk_fast_set Int.compare (filter is_macro carved)
        val depl2 = mk_fast_set Int.compare 
          (depl1 @ List.concat (map dep_of depl1))
        val defl = map (fn x => Vector.sub (!macrov,index_macro x))
          (dict_sort Int.compare depl2)
        val recmacro = lconcatw hashop (defl @ [carved])
      in
        recmacro
      end
    val macrol3 = map expandi (number_snd 0 macrol2)
    val progll = map collect_prog macrol3
    fun f (progl,orgseq) = map (fn (p,a,b) => (p, subseq (a,b) orgseq)) progl
    val l0 = combine (progll,macrol2)
    val l1 = List.concat (map f l0)
    val l2 = map_snd depsize_of l1
  in
    l2
  end


end (* struct *)

(*
load "macro"; open kernel aiLib macro;


fun merge_macrol macrol =
  let
    val d = ref (dempty prog_compare) 
    val cmp = cpl_compare Int.compare (list_compare Int.compare); 
    fun f (a,b) = 
      case dfindo a (!d) of
        NONE => d := dadd a b (!d)
      | SOME b' => if cmp (b,b') = LESS then d := dadd a b (!d) else ()
    val _ = app f macrol
  in
    dlist (!d)
  end;

fun one_macrol () = 
  let 
    val macro = random_macro (random_int (20,200)) 
    val l1 = collect_prog_standalone macro
    val l2 = map (fn (a,b) => (a,(length b,b))) l1
    val l3 = merge_macrol l2
  in
    l3
  end;
  
PolyML.print_depth 2;
val macroll = List.tabulate (100, fn _ => one_macrol ());
PolyML.print_depth 10;
val candl = merge_macrol (List.concat macroll);
length candl;
  
  
(* create candidates *)
fun create_cand k = 
  let
    val (macroll,t) = add_time List.tabulate (1000, fn _ => one_macrol ());
    val _ = print_endline ("generation: " ^ rts_round 2 t)
    val (candl,t) = add_time merge_macrol (List.concat macroll);
    val _ = print_endline ("merging: " ^ rts_round 2 t)
    val _ = print_endline ("candl: " ^ its (length candl))
  in
    candl
  end;
 
val candl = create_cand 100;

(* check candidates *)

val wind = ref (dempty Int.compare)
val partwind = ref (dempty Int.compare)  

fun checkf (p,exec) = 
  let
    val (anumtl,cov,anumlpart) = coverf_oeis exec
    fun f (anum,t) = update_wind wind (anum,[(t,p)])
    fun g (anum,n) = 
      if n <= 2 then () else update_partwind partwind (anum,(n,p))
  in
    app f anumtl;
    app g (create_anumlpart (anumtl,cov,anumlpart))
  end

fun checkonline (p,exec) = (init_fast_test (); checkf (p,exec))

fun checkinit () = (wind := dempty Int.compare; partwind := dempty Int.compare)

fun checkfinal () =
  let
    val _ = print_endline ("solutions: " ^ its (dlength (!wind))) 
    fun checkb p = (init_slow_test (); checkf (p, mk_exec p))
    val bestpl0 = dlist (!partwind)
    val bestpl1 = mk_fast_set prog_compare_size 
      (map snd (List.concat (map snd bestpl0)))
    val _ = partwind := dempty Int.compare
    val _ = print_endline ("checkb: " ^ its (length bestpl1))
    val (_,t) = add_time (app checkb) bestpl1
    val _ = print_endline ("checkb time: "  ^ rts_round 2 t ^ " seconds")
    val _ = print_endline ("more solutions: " ^ its (dlength (!wind)))  
    val r = dlist (!wind)
  in
    checkinit (); r
  end
  
fun collect_candidate () = 
  let 
    val pl1 = List.concat (map (map snd o snd) (dlist (!wind)))
    val pl2 = List.concat (map (map snd o snd) (dlist (!partwind)))
  in
    mk_fast_set prog_compare_size (pl1 @ pl2)
  end
  
fun checkpl pl =
  let 
    val i = ref 0 
    fun f p = (
      init_fast_test (); 
      incr i; 
      if !i mod 10000 = 0 then print "."  else ();
      checkf (p, mk_exec p)
      )
  in
    checkinit (); app f pl; checkfinal ()
  end

*)

(*
(* don't do any minimization, collect their definitional size 
   size of their necessary definitions + 
   size of 
   + reindex definitions 
 *)


*)


