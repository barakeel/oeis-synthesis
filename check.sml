structure check :> check =
struct

open HolKernel Abbrev boolLib aiLib smlParallel 
  mcts kernel bloom human exec game

val ERR = mk_HOL_ERR "check"
type anum = bloom.anum
type prog = kernel.prog
type ('a,'b) dict = ('a,'b) Redblackmap.dict

(* -------------------------------------------------------------------------
   Update set of solutions
   ------------------------------------------------------------------------- *)
   
fun update_wind_one d (anum,p) =
  case dfindo anum (!d) of 
    NONE => d := dadd anum p (!d)
  | SOME oldp =>
    if prog_compare_size (p,oldp) = LESS
    then d := dadd anum p (!d)
    else ()

fun merge_isol isol = 
  let val d = ref (dempty Int.compare) in
    app (update_wind_one d) isol;
    dlist (!d)
  end

fun compare_to (t1,t2) = case (t1,t2) of
    (NONE,NONE) => EQUAL
  | (SOME _, NONE) => LESS
  | (NONE, SOME _) => GREATER
  | (SOME x1, SOME x2) => Int.compare (x1,x2)

fun inv_cmp cmp (a,b) = cmp (b,a)
val compare_eff = cpl_compare (inv_cmp Int.compare) compare_to

fun update_partwind_one d (anum,(eff,p)) =
  case dfindo anum (!d) of 
    NONE => d := dadd anum [(eff,p)] (!d)
  | SOME oldl => 
    let
      fun test1 (oldeff,oldp) = 
        prog_compare_size (p,oldp) = LESS orelse 
        compare_eff (eff,oldeff) = LESS
      fun test2 (oldeff,oldp) =
        prog_compare_size (p,oldp) <> GREATER andalso 
        compare_eff (eff,oldeff) <> GREATER
    in
      if all test1 oldl
      then d := dadd anum ((eff,p) :: filter (not o test2) oldl) (!d) 
      else ()      
    end

fun merge_partisol partisol = 
  let 
    val d = ref (dempty Int.compare)
    fun f (anum,npl) = app (fn x => (update_partwind_one d) (anum,x)) npl 
  in
    app f partisol;
    dlist (!d)
  end
  
(* -------------------------------------------------------------------------
   Check if a program is a solution (i.e) covers an OEIS sequence
   ------------------------------------------------------------------------- *)

fun create_anumlpart (anuml,(n,to),anumlpart1) =
  let 
    fun f x = (length (valOf (Array.sub (oseq, x))), to)
    fun g x = (n, to)
  in
    map_assoc f anuml @ map_assoc g anumlpart1
  end
 
val wind = ref (dempty Int.compare)
val partwind = ref (dempty Int.compare)  

fun checkf (p,exec) = 
  let
    val (anuml,eff,anumlpart1) = coverf_oeis exec
    fun f anum = update_wind_one wind (anum,p)
    fun g (anum,eff) = update_partwind_one partwind (anum,(eff,p))
  in
    app f anuml;
    app g (create_anumlpart (anuml,eff,anumlpart1))
  end

fun checkonline (p,exec) = (init_fast_test (); checkf (p,exec))
fun checkp p = checkf (p, mk_exec p)
fun checkinit () = (wind := dempty Int.compare; partwind := dempty Int.compare)

fun checkfinal () = 
  let
    val _ = print_endline ("solutions: " ^ its (dlength (!wind))) 
    fun checkb p = (init_slow_test (); checkp p; init_fast_test ())
    val bestpl1 = mk_fast_set prog_compare 
      (map snd (List.concat (map snd (dlist (!partwind)))))
    val _ = partwind := dempty Int.compare
    val _ = print_endline ("checkb: " ^ its (length bestpl1))
    val bestpl2 = dict_sort prog_compare_size bestpl1
    val (_,t) = add_time (app checkb) bestpl2
    val _ = print_endline ("checkb time: "  ^ rts_round 2 t ^ " seconds")
    val _ = print_endline ("more solutions: " ^ its (dlength (!wind)))  
    fun forget ((a,b),c) = (a,c)
  in
    dlist (!wind)
  end    

end (* struct *)
