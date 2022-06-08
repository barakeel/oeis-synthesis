structure check :> check =
struct

open HolKernel Abbrev boolLib aiLib smlParallel 
  mcts kernel bloom human exec game

val ERR = mk_HOL_ERR "check"
type anum = bloom.anum
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

fun update_partwind_one d (anum,(ncover,p)) =
  case dfindo anum (!d) of 
    NONE => d := dadd anum [(ncover,p)] (!d)
  | SOME oldl => 
    let
      fun test1 (oldncover,oldp) = 
        prog_compare_size (p,oldp) = LESS orelse ncover > oldncover 
      fun test2 (oldncover,oldp) =
        prog_compare_size (p,oldp) <> GREATER andalso ncover >= oldncover 
    in
      if all test1 oldl
      then d := dadd anum ((ncover,p) :: filter (not o test2) oldl) (!d) 
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

fun create_anumlpart (anuml,ncover,anumlpart1) =
  let 
    fun f x = length (valOf (Array.sub (oseq, x)))
    fun g x = ncover
  in
    map_assoc f anuml @ map_assoc g anumlpart1
  end
 
fun check progl =
  let
    val wind = ref (dempty Int.compare)
    val partwind = ref (dempty Int.compare)
    fun checkx p =
      let
        val (anuml,ncover,anumlpart1) = coverp_oeis p
        fun f anum = update_wind_one wind (anum,p)
        fun g (anum,ncover) = update_partwind_one partwind (anum,(ncover,p))
      in
        app f anuml;
        app g (create_anumlpart (anuml,ncover,anumlpart1))
      end
    fun checka p = (timeincr := short_timeincr; checkx p)
    fun checkb p = (timeincr := long_timeincr; checkx p; 
                    timeincr := short_timeincr)
    val _ = print_endline ("checka start: " ^ its (length progl))
    val (_,t) = add_time (app checka) progl
    val _ = print_endline ("checka time: "  ^ rts_round 2 t ^ " seconds")
    val _ = print_endline ("solutions: " ^ its (dlength (!wind))) 
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
    (dlist (!wind), dlist (!partwind))
  end  
  
end (* struct *)
