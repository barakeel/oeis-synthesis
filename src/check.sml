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

fun is_faster (t1,p1) (t2,p2) =   
  cpl_compare Int.compare prog_compare_size ((t1,p1),(t2,p2)) = LESS
 
fun is_smaller (t1,p1) (t2,p2) = 
  prog_compare_size (p1,p2) = LESS

fun find_min_loop cmpf a m = case m of
    [] => a
  | a' :: m' => find_min_loop cmpf (if cmpf a' a then a' else a)  m'

fun find_min cmpf l = case l of 
    [] => raise ERR "find_min" ""
  | a :: m => find_min_loop cmpf a m


fun update_ifnew d anum (tpl,newtpl) = 
  if list_compare (snd_compare prog_compare) (tpl,newtpl) = EQUAL 
  then () 
  else d := dadd anum newtpl (!d)

fun update_smallest d anum tpl =
  let val newtpl = [find_min is_smaller tpl] in
    update_ifnew d anum (tpl,newtpl)
  end
  
fun update_fastest d anum tpl =
  let val newtpl = [find_min is_faster tpl] in
    update_ifnew d anum (tpl,newtpl)
  end  
   
fun update_sol2 d anum tpl =
  let val newtpl = mk_fast_set (snd_compare prog_compare) 
    [find_min is_smaller tpl, find_min is_faster tpl]
  in
    update_ifnew d anum (tpl,newtpl)
  end

fun update_wind d (anum,toptpl) =
  case dfindo anum (!d) of 
    NONE => d := dadd anum toptpl (!d)
  | SOME oldtpl =>
    let val tpl = toptpl @ oldtpl in
      if !sol2_flag then update_sol2 d anum tpl
      else if !t_flag then update_fastest d anum tpl
      else update_smallest d anum tpl
    end

fun merge_itsol itsol = 
  let val d = ref (dempty Int.compare) in
    app (update_wind d) itsol;
    dlist (!d)
  end

fun compare_to (t1,t2) = case (t1,t2) of
    (NONE,NONE) => EQUAL
  | (SOME _, NONE) => LESS
  | (NONE, SOME _) => GREATER
  | (SOME x1, SOME x2) => Int.compare (x1,x2)

fun inv_cmp cmp (a,b) = cmp (b,a)
val compare_cov = inv_cmp Int.compare

fun update_partwind d (anum,(cov,p)) =
  case dfindo anum (!d) of 
    NONE => d := dadd anum [(cov,p)] (!d)
  | SOME oldl => 
    let
      fun test1 (oldcov,oldp) = 
        prog_compare_size (p,oldp) = LESS orelse 
        compare_cov (cov,oldcov) = LESS
      fun test2 (oldcov,oldp) =
        prog_compare_size (p,oldp) <> GREATER andalso 
        compare_cov (cov,oldcov) <> GREATER
    in
      if all test1 oldl
      then d := dadd anum ((cov,p) :: filter (not o test2) oldl) (!d) 
      else ()      
    end

(* -------------------------------------------------------------------------
   Check if a program is a solution (i.e) covers an OEIS sequence
   ------------------------------------------------------------------------- *)

fun create_anumlpart (anumtl,n,anumlpart) =
  let 
    fun f (anum,_) = (anum, length (valOf (Array.sub (oseq, anum))))
    fun g anum = (anum, n)
  in
    map f anumtl @ map g anumlpart
  end
 
val wind = ref (dempty Int.compare)
val partwind = ref (dempty Int.compare)  

fun checkf (p,exec) = 
  let
    val (anumtl,cov,anumlpart) = coverf_oeis exec
    fun f (anum,t) = update_wind wind (anum,[(t,p)])
    fun g (anum,n) = update_partwind partwind (anum,(n,p))
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
    val bestpl0 = filter (fn x => not (dmem (fst x) (!wind))) 
      (dlist (!partwind))
    val bestpl1 = mk_fast_set prog_compare_size 
      (map snd (List.concat (map snd bestpl0)))
    val _ = partwind := dempty Int.compare
    val _ = print_endline ("checkb: " ^ its (length bestpl1))
    val (_,t) = add_time (app checkb) bestpl1
    val _ = print_endline ("checkb time: "  ^ rts_round 2 t ^ " seconds")
    val _ = print_endline ("more solutions: " ^ its (dlength (!wind)))  
    fun forget ((a,b),c) = (a,c)
  in
    dlist (!wind)
  end

end (* struct *)
