structure arcagi :> arcagi = struct

open HolKernel Abbrev boolLib aiLib dir kernel human json
val ERR = mk_HOL_ERR "arc_agi"

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


(*
load "json"; open json;
load "kernel"; open kernel;
load "aiLib"; open aiLib;
load "arcagi"; open argagi;
val dir = selfdir ^ "/data/arc-agi/training";
val filel = map (fn x => dir ^ "/" ^ x) (listDir dir);
val ERR = mk_HOL_ERR "arc_agi";
val exl = map read_ex filel;




*)


end (* struct *)   



