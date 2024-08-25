structure arcagi :> arcagi = struct

open HolKernel Abbrev boolLib aiLib dir kernel human json
val ERR = mk_HOL_ERR "arc_agi"

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
fun dest_number y = case y of NUMBER x => x
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
  let 
    val _ = print_endline file
    val json = parse (hd (readl file)) 
  in
    read_traintest (dest_ok json)
  end

(* --------------------------------------------------------------------------
   Evaluating a program on the training part of one example
   -------------------------------------------------------------------------- *)

(* 
I have a function f of two variables 
    val _ = mati_glob := mati
    val _ = dimo_glob := dimo
    val _ = colo_glob := colo
    val g = create_f 


f is a function from indices to color
*)


fun match_output f m = 
  let
    val (a,b) = Array2.dimensions m
    fun test (x,y) = f(x,y) = Array2.sub(m,x,y)
    val m' = Array2.tabulate Array2.RowMajor (a,b,test)
    val counter = ref 0
    fun count x = if x then incr counter else ()
    val _ = counter := 0
    val errors = (Array2.app Array2.RowMajor count m'; !counter)
    val errorwidth = if f(0,b) < 0 then 1 else 0
    val errorheight = if f(a,0) < 0 then 1 else 0
    val sc = errors + errorwidth + errorheight
  in
    (sc = a*b+2, sc)   
  end  


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
load "json"; open json;
load "kernel"; open kernel;
load "aiLib"; open aiLib;
load "arcagi"; open arcagi;


fun f (x,y) = if x + y >= 10 then ~1 else 0;
val m = compute_output f;
val sc = match_output f m;

val dir = selfdir ^ "/data/arc-agi/training";
val filel = map (fn x => dir ^ "/" ^ x) (listDir dir);
val ERR = mk_HOL_ERR "arc_agi";
val exl = map read_ex filel;

*)


end (* struct *)   



