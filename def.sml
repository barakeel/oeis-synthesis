structure def :> def =
struct

open HolKernel Abbrev boolLib aiLib dir kernel human;
val ERR = mk_HOL_ERR "def";

(* -------------------------------------------------------------------------
   Program with holes
   Start with top symbols and see how many subterms have this
   top symbols and go from hereS
   ------------------------------------------------------------------------- *)

val hole_id = ~1
val hole = Ins (hole_id,[])

fun prog_size_nohole (Ins(s,pl)) = 
  if s = hole_id then 0 else (1 + sum_int (map prog_size_nohole pl))

local fun insert l posi newa =
  let fun f i a = if i = posi then newa else a in
    mapi f l
  end
in
  fun all_holes (p as Ins (id,pl)) = 
    Ins (hole_id,[]) :: map (fn x => Ins (id,x)) (all_holes_pl pl)

  and all_holes_pl pl = 
    let 
      val l = map all_holes pl
      fun f i x = map (insert pl i) x
    in
      List.concat (mapi f l)
    end
end

fun inst_pat_aux (pat as (Ins (id,patl))) instl =  
  if id = ~1 then 
   (case instl of [] => (pat,[]) | a :: m => (a,m))
  else
    let val (argl,newinstl) = inst_patl_aux [] patl instl in
      (Ins (id, argl), newinstl)
    end
and inst_patl_aux argl patl instl = case patl of 
    [] => (rev argl, instl)
  | pata :: patm =>
    let val (arga,newinstl) = inst_pat_aux pata instl in
      inst_patl_aux (arga :: argl) patm newinstl
    end
  
fun inst_pat pat instl = 
  let val (p,newinstl) = inst_pat_aux pat instl in
    if not (null newinstl) then raise ERR "inst_pat" "too many" else p
  end

fun has_hole (Ins (id,pl)) = 
  if id = hole_id then true else exists has_hole pl

fun count_hole (Ins (id,pl)) = 
  if id = hole_id then 1 else sum_int (map count_hole pl)

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


(*
load "kernel"; open kernel;
val p = inst_pat  (Ins (3,[Ins(~1,[]),Ins (4,[Ins(~1,[])])])) [(Ins (2,[])),(Ins (5,[]))];
*)

(* definitions *)
val def_id = Vector.length operv

fun mk_def pat =
  if not (has_hole pat) then
  let fun f l = case l of [] => pat | _ => raise ERR "defd" "" in
    f
  end
  else inst_pat pat

val defl = 
  let val patfile = selfdir ^ "/pat" in
    if exists_file patfile
    then number_fst def_id (read_progl patfile) 
    else []
  end

val defd = dnew Int.compare (map_snd mk_def defl);

fun undef_prog (Ins (id,pl)) = 
  if not (dmem id defd) then Ins (id, map undef_prog pl) else
  let val newp = (dfind id defd) pl in 
    undef_prog newp 
  end

val def_operl = 
  map (fn (i,pat) => mk_var ("def" ^ its i,
    rpt_fun_type (count_hole pat + 1) alpha)) defl;

(* -------------------------------------------------------------------------
   Make definitions
   ------------------------------------------------------------------------- *)

fun compression sol pat =
  let val sol2 = map (psubst (pat,~2)) sol in
    sum_int (map prog_size sol2)
  end

fun best_def sol =
  let 
    val l0 = dlist 
      (count_dict (dempty prog_compare) (List.concat (map all_subprog sol)))
    fun distr_holes (a,i) = map (fn x => (x,i)) (all_holes a);
    val l1 = List.concat (map distr_holes l0);
    val l2 = dlist (dsum prog_compare (l0 @ l1));
    fun f (p,freq) = (p , (prog_size_nohole p - 1) * freq)
    val l21 = map f l2
    val l22 = filter (fn (a,b) => prog_size a >= 2 andalso b >= 100) l21
    val l23 = dict_sort compare_imax l22
    val l3 = first_n 200 l23
    val _ = print_endline ("preselection: " ^ its (length l3))
    val l4 = map (fn (a,_) => (a, compression sol a)) l3;
    val l5 = dict_sort compare_imin l4;
  in
    fst (hd l5)
  end

fun nbest_def ntop soltop = 
  let 
    val ntottop = sum_int (map prog_size soltop)
    val _ =  print_endline ("total size: " ^ its ntottop)
    fun loop defl n defn sol =
      if n <= 0 then (rev defl, sol) else
      let 
        val def = best_def sol
        val _ = print_endline (humanf def)
        val newsol = map (psubst (def,defn)) sol
        val ntot = sum_int (map prog_size newsol)
        val _ =  print_endline ("total size: " ^ its ntot)
      in
        loop ((def,defn) :: defl) (n-1) (defn + 1) newsol
      end
  in
    loop [] ntop def_id soltop
  end

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

fun gain (a,b) = let val r = Real.fromInt (hsize a - 1) in 
  if r <= 7.1 then 0.0 else Math.pow (1.1,r) * Real.fromInt b
  end; 
  
fun b_def cutoff sol =
  let 
    val atree = create_atree cutoff sol;
    val defl = collect_def atree;   
    val defl1 = dict_sort compare_imax defl;
    val defl2 = map_assoc gain defl1;
    val defl3 = dict_sort compare_rmax defl2;
    val def = (fst o fst) (hd defl3)
    (*
    val l3 = map (fst o fst) (first_n 100 defl3)
    val l4 = map_assoc (compression sol) l3;
    val l5 = dict_sort compare_imin l4;
    *)
  in
    def
  end

fun nb_def cutoff ntop soltop = 
  let 
    val ntottop = sum_int (map prog_size soltop)
    val _ =  print_endline ("total size: " ^ its ntottop)
    fun loop defl n defn sol =
      if n <= 0 then (rev defl, sol) else
      let 
        val def = b_def cutoff sol
        val _ = print_endline (humanf def)
        val arity = nhole def
        val _ = arityd := dadd defn arity (!arityd) 
        val newsol = map (psubst (def,defn)) sol
        val ntot = sum_int (map prog_size newsol)
        val _ =  print_endline ("total size: " ^ its ntot)
      in
        loop ((def,defn) :: defl) (n-1) (defn + 1) newsol
      end
  in
    loop [] ntop def_id soltop
  end
  
  

end (* struct *)


(* 
load "def"; open aiLib kernel human def;
val isol = read_iprogl "model/isol100";
val sol = map snd isol;
PolyML.print_depth 2;
val x = nb_def 100 10 sol;



*)
