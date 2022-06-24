structure def :> def =
struct

open HolKernel Abbrev boolLib aiLib dir kernel human;
val ERR = mk_HOL_ERR "def";

(* -------------------------------------------------------------------------
   Replace a pattern (top of a program) by its number
   compressing programs
   ------------------------------------------------------------------------- *)

exception Pmatch;
fun pmatch_aux (pat as Ins (id1,pl1), p as Ins (id2,pl2)) = 
  if id1 = hole_id then [p]
  else if id1 = id2 andalso length pl1 = length pl2 then
    List.concat (map pmatch_aux (combine (pl1,pl2)))
  else raise Pmatch;

fun pmatch pat p = (SOME (pmatch_aux (pat,p)) handle Pmatch => NONE);

fun psubst (pat,id2) (ptop as Ins (id,pl)) = case pmatch pat ptop of
    SOME argl => Ins (id2, map (psubst (pat,id2)) argl)
  | NONE => Ins (id, map (psubst (pat,id2)) pl);
 
fun psubstl pil p = foldl (uncurry psubst) p pil;

(* -------------------------------------------------------------------------
   Make definitions top-down. 
   ------------------------------------------------------------------------- *)

datatype atree = ANode of (prog * (prog list * int) list * 
  (int,atree) dict list)

val hole2 = Ins (~2,[])

val arityl = List.tabulate (Vector.length operv, fn x => (x,arity_of_oper x)) 
val arityd = ref (dnew Int.compare arityl)
fun pat_id id = Ins (id, List.tabulate (dfind id (!arityd), fn _ => hole))

fun split_plil n plil =
  if n <= 0 then [] else plil :: split_plil (n-1) (map_fst tl plil) 

fun update_dict def offset ((pl,freq),d) =
  if null pl then raise ERR "udpate_vect" "" else
  let 
    val Ins (id,arg) = hd pl
    val newpl = arg @ tl pl
    val newat = case dfindo id d of
      NONE => 
      let val newdef = inst_pat def 
        (List.tabulate (offset, fn _ => hole2) @ [pat_id id])
        handle HOL_ERR _ => raise ERR "update_dict" (its offset ^ ": " ^ 
          humanf def ^ " | " ^ humanf (hd pl)) 
      in    
        ANode (newdef, [(newpl,freq)], []) 
      end
      | SOME (ANode (def,plil,_)) =>
        ANode (def, (newpl,freq) :: plil, [])
  in
    dadd id newat d 
  end

fun expand_anode cutoff (attop as (ANode (def,plil,_))) =
  if sum_int (map snd plil) < cutoff then attop else
  let 
    val n = length (fst (hd plil)) handle Empty => raise ERR "expand_anode" ""
    val ncover = sum_int (map snd plil)
    val _ = debug (humanf def ^ " " ^ its ncover)
  in
  if n <= 0 orelse prog_size def > 20 then attop else  
  let
    val plill = split_plil n plil handle Empty => raise ERR "expand_anode" ""
    fun f offset x = foldl (update_dict def offset) (dempty Int.compare) x
    val vl1 = mapi f plill
    val vl2 = map (dmap ((expand_anode cutoff) o snd)) vl1
  in
    ANode (def, plil, vl2)     
  end  
  end
  
fun create_atree cutoff sol = 
  let 
    val pil = dlist 
      (count_dict (dempty prog_compare) (List.concat (map all_subprog sol)))
  in
    expand_anode cutoff (ANode (hole, map_fst (fn x => [x]) pil, []))
  end

(* -------------------------------------------------------------------------
   Extract definitions top-down
   ------------------------------------------------------------------------- *)

fun collect_def_aux r (ANode (def,plil,dl)) =
  let 
    val _ = r := (def,sum_int (map snd plil)) :: !r
    fun f d = app (collect_def_aux r) (map snd (dlist d)) 
  in
    app f dl  
  end
  
fun collect_def atree =
  let 
    fun g (Ins (a,pl)) = if a = ~2 then Ins (~1,[]) else Ins (a,map g pl);
    val r = ref [] 
  in 
    collect_def_aux r atree; 
    map_fst g (!r)
  end
 
fun hsize (Ins (id,pl)) = (if id = ~1 then 0 else 1) + sum_int (map hsize pl);
fun nhole (Ins (id,pl)) = (if id = ~1 then 1 else 0) + sum_int (map nhole pl);

fun gain (a,b) = if prog_size a <= 1 then ~1 else (hsize a - 1) * b

fun b_def cutoff sol =
  let 
    val atree = create_atree cutoff sol;
    val defl1 = collect_def atree;   
    val defl2 = map (fn (a,b) => (a,gain (a,b))) defl1
    val defl3 = map fst (dict_sort compare_imax defl2)
    val defl4 = filter (fn x => snd x <= maxarity) (map_assoc nhole defl3);
  in
    fst (hd defl4)
  end

fun nb_def cutoff ntop soltop = 
  let 
    val ntottop = sum_int (map (prog_size o snd) soltop)
    val _ =  print_endline ("total size: " ^ its ntottop)
    fun loop defl n defn sol =
      if n <= 0 then (rev defl, sol) else
      let 
        val def = b_def cutoff (map snd sol)
        val _ = print_endline (humanf def)
        val arity = nhole def
        val _ = arityd := dadd defn arity (!arityd) 
        val newsol = map_snd (psubst (def,defn)) sol
        val ntot = sum_int (map (prog_size o snd) newsol)
        val _ =  print_endline ("total size: " ^ its ntot)
      in
        loop ((def,defn) :: defl) (n-1) (defn + 1) newsol
      end
  in
    loop [] ntop def_id soltop
  end
  
end (* struct *)


(* 
PolyML.print_depth 2;
load "def"; open aiLib kernel human def;
val isol = read_iprogl "exp/603/hist/boot211");
val (defl,newisol) = nb_def 100 (96-14) isol;
write_progl "def" (map fst defl);
write_iprogl "exp/603/hist/isol0" newisol; 
*)
