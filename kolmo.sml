structure kolmo :> kolmo =
struct

open HolKernel Abbrev boolLib 
  aiLib mlTreeNeuralNetworkAlt smlParallel kernel bloom 
val ERR = mk_HOL_ERR "kolmo";

(* -------------------------------------------------------------------------
   Datastructures
   ------------------------------------------------------------------------- *)

val seltemp = ref []
val seld = ref (dempty Int.compare)
val semb = BoolArray.tabulate (bmod, fn _ => false)
val winl = ref []
val wind = ref (eempty seq_compare)

val sem_counter = ref 0
val div_counter = ref 0
fun semtoseq x = first_n 16 x
val quotient_flag = ref true

(* -------------------------------------------------------------------------
   Store in selection dictionnary + increment counters
   ------------------------------------------------------------------------- *)

fun update_wind p sem =
  let 
    val winseql = find_wins p sem
    val b = ref false
    fun f x = if not (emem x (!wind)) 
      then (wind := eadd x (!wind); b := true) else ()
  in
    app f winseql;
    if !b then winl := p :: !winl else ()
  end

fun to_seld f x = 
  let 
    val _ = check_timer () 
    val p = f x
    val f = let val exec = start (mk_exec p) in
        (fn x => exec x handle Overflow => error)
      end
    val semo = SOME (map f entryl) handle Div => (incr div_counter; NONE)
  in
   case semo of NONE => () | SOME sem => 
   (
   update_wind p sem;
   if !quotient_flag andalso bmem sem semb then incr sem_counter else
     (seltemp := zip_prog p :: !seltemp; badd sem semb)
   )
  end

val piapp_nullop = papp_nullop
fun piapp_binop id (a,b) = papp_binop id (unzip_prog a, unzip_prog b)
fun piapp_ternop id (a,b,c) = 
  papp_ternop id (unzip_prog a, unzip_prog b, unzip_prog c)

fun papp_nullop_seld x = to_seld piapp_nullop x
fun papp_binop_seld x y = to_seld (piapp_binop x) y
fun papp_cond_seld y = to_seld (piapp_ternop cond_id) y
fun papp_loop_seld y = to_seld (piapp_ternop loop_id) y

(* -------------------------------------------------------------------------
   Generating all inputs at depth dep for a function with arity ari.
   ------------------------------------------------------------------------- *)

fun numpart k n = number_partition k n handle HOL_ERR _ => [];

fun iter_cpl2 f (v1,v2) = 
  let 
    val n1 = Vector.length v1
    val n2 = Vector.length v2
    fun loop i j =
      if i >= n1 then loop 0 (j+1)
      else if j >= n2 then () else
      (f (Vector.sub (v1,i), Vector.sub (v2,j));
       loop (i+1) j)
  in
    loop 0 0
  end

fun iter_part2 dep f = 
  let 
    val partl1 = map pair_of_list (numpart 2 dep) 
    fun g i = dfind i (!seld) handle NotFound => (Vector.fromList [])
    val partl2 = map (fn (a,b) => (g a, g b)) partl1
  in
    app (iter_cpl2 f) partl2
  end

fun app_all_binop dep operl =
  app (fn x => iter_part2 dep (papp_binop_seld x)) operl;

fun iter_cpl3 f (v1,v2,v3) = 
  let 
    val n1 = Vector.length v1
    val n2 = Vector.length v2
    val n3 = Vector.length v3
    fun loop i j k =
      if i >= n1 then loop 0 (j+1) k
      else if j >= n2 then loop 0 0 (k+1) 
      else if k >= n3 then ()
      else
      (f (Vector.sub (v1,i), Vector.sub (v2,j), Vector.sub (v3,k));
       loop (i+1) j k)
  in
    loop 0 0 0
  end

fun iter_part3 dep f = 
  let 
    val partl1 = map triple_of_list (numpart 3 dep) 
    fun g i = dfind i (!seld) handle NotFound => (Vector.fromList [])
    val partl2 = map (fn (a,b,c) => (g a, g b, g c)) partl1
  in
    app (iter_cpl3 f) partl2
  end

(* -------------------------------------------------------------------------
   Exhaustive bottom-up search
   ------------------------------------------------------------------------- *)

fun debug_rl l = debug (String.concatWith " " (map (rts_round 3) l))

fun kolmo_one_aux dep =
  let
    val _ = seltemp := []
    val _ = debug "binop"
    val (_,t1) = add_time (app_all_binop dep) binaryidl
    val _ = debug "cond"
    val (_,t2) = add_time (iter_part3 dep) papp_cond_seld
    val _ = debug "loop"
    val (_,t3) = add_time (iter_part3 dep) papp_loop_seld
    val _ = debug_rl [t1,t2,t3]
    val v = Vector.fromList (!seltemp)
    val _ = seld := dadd dep v (!seld)
  in
    debug ("new: " ^ its (Vector.length v));
    print_endline 
      ("total: " ^ its (
       sum_int (map (Vector.length o snd) (dlist (!seld)))));
    print_endline ("solutions: " ^  its (elength (!wind)));
    print_endline ("sol prog: " ^  its (length (!winl)))
  end

fun kolmo_one dep =
  let 
    val (_,t) = add_time kolmo_one_aux dep 
  in
     debug (String.concatWith ", " [
      "step:" ^ its dep ^ " " ^ its (!rti_glob),
      "time:" ^ rts_round 3 t])
  end

fun init_kolmo () =
  (
  init_timer ();
  seld := dempty Int.compare; seltemp := [];
  div_counter := 0;
  sem_counter := 0;
  app papp_nullop_seld nullaryidl;
  seld := dadd 1 (Vector.fromList (!seltemp)) (dempty Int.compare);
  print_endline 
      ("total: " ^ its (sum_int (map (Vector.length o snd) (dlist (!seld)))));
    print_endline ("solutions: " ^  its (elength (!wind)));
    print_endline ("sol prog: " ^  its (length (!winl)))
  )

fun kolmo maxdep =
  let
    val startsize = 2
    fun loop n = if n > maxdep then () else (kolmo_one n; loop (n + 1))  
  in
    init_kolmo (); loop startsize
  end

fun all_subseq_aux seq = case seq of
    [] => [[]]
  | a :: m => seq :: all_subseq_aux m

fun all_subseq seq = map rev (all_subseq_aux (rev seq))

fun stats () =
  let
    val tot = !rti_glob
    val divc = !div_counter
    val semc = !sem_counter
  in
    print_endline ("\ntotal:       " ^  its tot);
    print_endline ("quotiented:  " ^  its semc);
    print_endline ("exceptions:  " ^ its divc);
    print_endline ("solutions:      " ^  its (elength (!wind)))
  end


end

(*
load "kolmo"; 
PolyML.print_depth 0; open aiLib kernel bloom kolmo; PolyML.print_depth 40;

search_time := Time.fromReal 1000.0;
debug_flag := false;
quotient_flag := false;
time kolmo 5;
stats ();
*)



(*
total:       24293300
quotiented:  18582806
exceptions:  959968
unique:      4750526
unique top:  4750526
solutions long:   4449
solutions short:   315

!overflow_counter; (negative numbers)
total:       23350500
quotiented:  17377311
exceptions:  1322704
unique:      4650485
unique top:  4650485
solutions long:   3389
solutions short:   231

total:       21967400
quotiented:  16518626
exceptions:  1322421
unique:      4126353
unique top:  4126353
solutions long:   3346
solutions short:   268

total:       36663900
quotiented:  24224448
exceptions:  8002150
unique:      4437302
win: 8692
realwin: 3503

7hash
total:       12518700
quotiented:  9140176
exceptions:  1319123
solutions:      2992

2hash
total:       19946500
quotiented:  15103483
exceptions:  1319123
solutions:      3171

7hash + dict
total:       14808000
quotiented:  10954044
exceptions:  1319396
solutions:      3083

7hash + dict + nocollision checking
total:       14808000
quotiented:  10954044
exceptions:  1319396
solutions:      3083

total:       19144100
quotiented:  13785601
exceptions:  3050831
solutions:      1690

total:       15195800
quotiented:  11335770
exceptions:  1319396
solutions:      3083

total:       27254800
quotiented:  21089765
exceptions:  1319416
solutions:      3427

total:       44874200
quotiented:  26292032
exceptions:  13075706
solutions:      3918

total:       45920800
quotiented:  27295461
exceptions:  13075706
solutions:      3919

total:       322207700
quotiented:  255549654
exceptions:  18300507
solutions:      6246

total:       25263500
quotiented:  19100883
exceptions:  1319406
solutions:      3426

total:       290972600
quotiented:  228900780
exceptions:  18300345
solutions:      6157

total:       36450300
quotiented:  23687801
exceptions:  7593816
solutions:      3695

total:       25754300
quotiented:  19584199
exceptions:  1319123
solutions:      3618


*)








