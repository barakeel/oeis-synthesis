structure ramsey :> ramsey = struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "ramsey"

fun extend_shapel test j shapel =
  map (fn x => j :: x) (filter test shapel)   
  
fun merge_ll ll1 ll2 = case (ll1,ll2) of
    (_,[]) => ll1 
  | ([],_) => ll2
  | (a1 :: m1, a2 :: m2) => (a1 @ a2) :: merge_ll m1 m2;

local open IntInf in
fun hash_bl_aux start bl = case bl of 
    [] => start
  | b :: m => hash_bl_aux (2 * start + (if b then 1 else 0)) m;
  
fun hash_bl bl = hash_bl_aux 1 bl;  
end;
   
val shapetimer = ref 0   

fun get_score klevel =
  let
    val il = map snd klevel
    val il1 = if length il < 4
              then List.tabulate (4 - length il,fn _ => 27) @ il
              else il
    val obj = [27,18,12,8]
    val scl = map (fn (a,b) => if a >= b then 0 else b - a) (combine (il1,obj))
  in
    ~(sum_int scl)
  end

exception RamseyTimeout;

fun next_shapel f endj ((bluell,redll),bl,klevel,j) = 
  if j >= endj then (get_score (butlast klevel), hash_bl bl) else
  let 
    val coloringl = List.tabulate (j, fn i => ([i,j],f (i,j)))
    val (blueedg,rededg) = partition snd coloringl
    val edgel = map fst (filter snd coloringl)
    val bluev = Vector.fromList (map snd coloringl)
    val redv = Vector.fromList (map (not o snd) coloringl)
    fun fblue shape = all 
      (fn x => (incr shapetimer; Vector.sub (bluev,x))) shape
    fun fred shape = all 
      (fn x => (incr shapetimer; Vector.sub (redv,x))) shape 
    val bluell1 = [] :: filter (not o null) 
      (map (extend_shapel fblue j) bluell)
    val redll1 = [] :: filter (not o null) 
      (map (extend_shapel fred j) redll)
    val bluell2 = merge_ll bluell1 bluell
    val redll2 = merge_ll redll1 redll
    val k = Int.max (length bluell2,length redll2) - 1
    val newklevel = if k <= fst (hd klevel) then klevel else (k,j+1) :: klevel
  in
    if !shapetimer >= 1000000 orelse k >= 8
      then raise RamseyTimeout
    else next_shapel f endj 
      ((bluell2,redll2),map snd coloringl @ bl,newklevel,j+1)
  end;

fun enum_shapel f = 
  (shapetimer := 0; next_shapel f 26 (([[[]]],[[[]]]),[],[(3,~1)],0))
  handle  Empty => (1,IntInf.fromInt 0) 
        | Div => (1,IntInf.fromInt 0)
        | ProgTimeout => (1,IntInf.fromInt 0)
        | Overflow => (1,IntInf.fromInt 0)
        | RamseyTimeout => (1,IntInf.fromInt 0);

fun ramsey_score p =
  let 
    val f0 = exec_memo.mk_exec p
    fun f1 (i,j) = (init_timer (); 
      hd (f0 ([IntInf.fromInt i],[IntInf.fromInt j])) >= 0)
  in
    enum_shapel f1
  end

end (* struct *)   



