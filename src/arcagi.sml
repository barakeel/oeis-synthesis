structure arcagi :> arcagi = struct

open HolKernel Abbrev boolLib aiLib dir kernel human json exec_memo
val ERR = mk_HOL_ERR "arc_agi"
type mat = int Array2.array

type ex = (mat * mat) list * (mat * mat) list

val defaultmat = Array2.tabulate Array2.RowMajor (1,1,fn (a,b) => 0);
val ex_glob = ref ([(defaultmat,defaultmat)],[(defaultmat,defaultmat)])
val exi_glob = ref 0
val trainex_glob = ref (Vector.fromList [])

(* --------------------------------------------------------------------------
   Reading the training examples
   -------------------------------------------------------------------------- *)

fun dest_traintest x = case x of OBJECT [("train",a),("test",b)] => (a,b)
  | OBJECT [("train",a),("test",b),("name",_)] => (a,b)
  | OBJECT [("test",a),("train",b),("name",_)] => (a,b)
  | OBJECT [("test",a),("train",b)] => (a,b)
  | _ => raise ERR "dest_traintest" ""

fun dest_ok y = case y of OK x => x | _ => raise ERR "dest_ok" ""
fun dest_object y = case y of OBJECT x => x | _ => raise ERR "dest_object" ""
fun dest_array y = case y of ARRAY x => x | _ => raise ERR "dest_array" ""
fun dest_io y = case y of OBJECT [("input",a),("output",b)] => (a,b)
  | _ => raise ERR "dest_io" "";  
fun dest_number y = case y of NUMBER x => Real.round x
  | _ => raise ERR "dest_number" "";  

fun read_line x = Vector.fromList (map dest_number (dest_array x))

fun ll_to_vv ll = Vector.fromList (map Vector.fromList ll)
    
fun vv_to_array vv =  
  let
    fun f (a,b) = Vector.sub (Vector.sub (vv,a),b) 
  in
    Array2.tabulate Array2.RowMajor (Vector.length vv, 
     Vector.length (Vector.sub (vv,0)), f)
  end

fun read_array x = 
  let val vv = Vector.fromList (map read_line (dest_array x)) in
    vv_to_array vv
  end

fun read_io x = let val (a,b) = dest_io x in (read_array a, read_array b) end
fun read_iol x = map read_io (dest_array x);
fun read_traintest x = 
  let val (a,b) = dest_traintest x in (read_iol a, read_iol b) end

fun read_ex file = 
  let val json = parse (hd (readl file)) in
    read_traintest (dest_ok json)
  end
  
fun read_trainex () = 
  let 
    val dir = selfdir ^ "/data/arc-agi/training"
    val filel = map (fn x => dir ^ "/" ^ x) (listDir dir)
    val r = map read_ex filel
    val _ = print_endline ("Read " ^ its (length r) ^ 
            " training examples from " ^ dir) 
  in
    trainex_glob := Vector.fromList r
  end

(* --------------------------------------------------------------------------
   Evaluating a program on the training part of one example
   -------------------------------------------------------------------------- *)

fun get_colorv matl = 
  let
    val d = ref (dempty Int.compare)
    val counter = ref 0 
    fun g x = 
      (if dmem x (!d) then () else d := dadd x (!counter) (!d);
       incr counter)   
    fun f mato = Array2.app Array2.RowMajor g mato
    val _ = app f matl
    val l = map fst (dict_sort (snd_compare Int.compare) (dlist (!d)))
  in
    Vector.fromList (0 :: filter (fn x => x <> 0) l)
  end

fun get_dimo matol = 
  let 
    val l = map Array2.dimensions matol 
    val set = enew (cpl_compare Int.compare Int.compare) l
    fun f (a,b) = (IntInf.fromInt a, IntInf.fromInt b)
  in
    f (if elength set = 1 then hd l else (0,0))
  end

fun mk_fun ex mati p = 
  let
    val _ = mati_glob := mati
    val matil = map fst (fst ex)
    val _ = coliv_glob := get_colorv matil
    val matol = map snd (fst ex)
    val colov = get_colorv matol
    val _ = dimo_glob := get_dimo matol
    fun fdim (a,b) = (IntInf.fromInt a, IntInf.fromInt b)
    val _ = dimi_glob := fdim (Array2.dimensions (!mati_glob))
    val _ = push_counter := 0
    val f0 = exec_memo.mk_exec p
    fun f1 (i,j) = 
      (
      abstimer := 0; 
      timelimit := !timeincr;
      let val rl = f0 ([IntInf.fromInt i], [IntInf.fromInt j]) 
                   handle Subscript => raise ERR "f0" ""
      in
        case rl of 
          [] => raise Empty
        | [x] => if 0 <= x andalso x < IntInf.fromInt (Vector.length colov)
                 then Vector.sub (colov, IntInf.toInt x)
                      handle Subscript => raise ERR "colov" ""
                 else ~1
        | x :: y :: _ => 
          if IntInf.fromInt 0 <= x andalso x < fst (!dimi_glob) andalso  
             IntInf.fromInt 0 <= y andalso y < snd (!dimi_glob)
          then Array2.sub (!mati_glob, IntInf.toInt x, IntInf.toInt y)
               handle Subscript => raise ERR "mati" ""
          else ~1
      end
      )
  in
    f1
  end
 
fun match_io ex p (mi,mo) = 
  let
    val f = mk_fun ex mi p
    val (a,b) = Array2.dimensions mo
    fun test (x,y) = f(x,y) = Array2.sub(mo,x,y)
    val mo' = Array2.tabulate Array2.RowMajor (a,b,test)
    val counter = ref 0
    fun count x = if x then incr counter else ()
    val _ = counter := 0
    val errors = (Array2.app Array2.RowMajor count mo'; !counter)
    val errorwidth = if f(0,b) < 0 then 1 else 0
    val errorheight = if f(a,0) < 0 then 1 else 0
    val sc = errors + errorwidth + errorheight
  in
    (sc = a*b+2, (sc * 1000 * 1000) div (a*b+2))
  end

fun score ex p =
  let val (bl,scl) = split (map (match_io ex p) (fst ex)) in                  
    SOME (all I bl, (sum_int scl * 1000) div (length scl))
  end
  handle     
    Empty => NONE
  | Div => NONE
  | ProgTimeout => NONE
  | Overflow => NONE 
  

fun compute_output f = 
  let
    fun mk_line0 y acc =
      if y >= 30 then rev acc else
      let val color = f (0,y) in
        if color < 0
        then rev acc 
        else mk_line0 (y+1) (color :: acc)
      end
    fun mk_line width x y acc =
      if y >= width then rev acc else
      mk_line width x (y+1) (f (x,y) :: acc)
    val line0 = mk_line0 0 []
    val width = length line0
    fun mk_mat x acc = 
      if x >= 30 then rev acc else
      let val color = f (x,0) in
      if color < 0 then rev acc else
        let val line = mk_line width x 1 [] in
          mk_mat (x+1) ((color :: line) :: acc)
        end
      end
  in
    if width = 0 then raise Match else 
    (vv_to_array o ll_to_vv) (line0 :: mk_mat 1 [])
  end;
  

(*
load "kernel"; open kernel;
load "aiLib"; open aiLib;
load "arcagi"; open arcagi;
load "game"; open game;
load "search";
PolyML.print_depth 1; val exl = read_trainex (); PolyML.print_depth 40;
 


val ex = random_elem exl;
val (p,b,sc) = test ex 10.0;

(* need to test on all input output pairs *)
*)
   

(*
load "json"; open json;
load "kernel"; open kernel;
load "aiLib"; open aiLib;
load "arcagi"; open arcagi;
val matol = map snd (fst (random_elem exl));
val exl' = distrib exl;
fun f (x,y) = if x + y >= 10 then ~1 else 0;
val m = compute_output f;
val sc = match_output f m;
*)


end (* struct *)   



