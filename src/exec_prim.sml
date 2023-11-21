(* ========================================================================= *)
(* Timed primitive functions                                                 *)
(* ========================================================================= *)

structure exec_prim :> exec_prim =
struct

open HolKernel aiLib kernel

local open IntInf in
val azero = fromInt 0
val aone = fromInt 1
val atwo = fromInt 2
val maxint = fromInt (valOf (Int.maxInt))
val minint = fromInt (valOf (Int.minInt))
fun large_int x = x > maxint orelse x < minint
end

fun checktimer () = 
  (
  incr abstimer;
  if !abstimer > !timelimit then raise ProgTimeout else ()
  )
  
fun mylog x = if x = 0 then 1 else IntInf.log2 x

fun cost f costn x1 x2 y = 
  if large_int x1 orelse large_int x2 orelse large_int y
  then f (mylog (IntInf.abs x1), mylog (IntInf.abs x2))
  else costn

fun checktimerf f costn x1 x2 y =
  (
  abstimer := !abstimer + cost f costn x1 x2 y;
  if !abstimer > !timelimit then raise ProgTimeout else y
  )

(* -------------------------------------------------------------------------
   Integer primitives
   ------------------------------------------------------------------------- *)

local open IntInf in
fun tzero () = (checktimer (); azero)
fun tone () = (checktimer (); aone)
fun ttwo () = (checktimer (); atwo)
fun taddi a1 a2 = checktimerf Int.max 1 a1 a2 (a1 + a2)
fun tdiff a1 a2 = checktimerf Int.max 1 a1 a2 (a1 - a2)
fun tmult a1 a2 = checktimerf FixedInt.+ 1 a1 a2 (a1 * a2)
fun tdivi a1 a2 = checktimerf FixedInt.+ 5 a1 a2 (a1 div a2)
fun tmodu a1 a2 = checktimerf FixedInt.+ 5 a1 a2 (a1 mod a2)
end

(* -------------------------------------------------------------------------
   Rational primitives
   ------------------------------------------------------------------------- *)

type rat = IntInf.int * IntInf.int

val r0 = (azero,aone)
val r1 = (aone,aone)
val r2 = (atwo,aone)

fun rzero () = (checktimer (); r0)
fun rone () = (checktimer (); r1)
fun rtwo () = (checktimer (); r2)

fun raddi (p1,q1) (p2,q2) = 
  if q1 = aone andalso q2 = aone 
  then (taddi p1 p2, aone)
  else (taddi (tmult p1 q2) (tmult p2 q1), tmult q1 q2)
  
fun rdiff (p1,q1) (p2,q2) = 
  if q1 = aone andalso q2 = aone 
  then (tdiff p1 p2, aone)
  else (tdiff (tmult p1 q2) (tmult p2 q1), tmult q1 q2) 

fun rmult (p1,q1) (p2,q2) = 
  if q1 = aone andalso q2 = aone
  then (tmult p1 p2, aone)
  else (tmult p1 p2, tmult q1 q2)
 
fun rdivr (p1,q1) (p2,q2) =  
  if p2 = azero then raise Div else
  (tmult p1 q2, tmult q1 p2)

fun rdivi (p1,q1) (p2,q2) = 
  if q1 = aone andalso q2 = aone
  then (tdivi p1 p2,aone)
  else raise Div
  
fun rmodu (p1,q1) (p2,q2) = 
  if q1 = aone andalso q2 = aone
  then (tmodu p1 p2,aone)
  else raise Div

fun is_rzero ((p1,q1):rat) = p1 = azero

fun numerator (p1,q1) = (checktimer (); (p1,aone))
fun denominator (p1,q1) = (checktimer (); (q1,aone))

(* -------------------------------------------------------------------------
   Complex primitives
   ------------------------------------------------------------------------- *)

type complex = rat * rat

val c0 = (r0,r0)
val c1 = (r1,r0)
val c2 = (r2,r0)
val ci = (r0,r1)

fun czero () = (checktimer (); c0)
fun cone () = (checktimer (); c1)
fun ctwo () = (checktimer (); c2)
fun cimag () = (checktimer (); ci)

fun caddi (a1,b1) (a2,b2) = 
  if is_rzero b1 andalso is_rzero b2
  then (raddi a1 a2, r0)
  else (raddi a1 a2, raddi b1 b2)
 
fun cdiff (a1,b1) (a2,b2) = 
  if is_rzero b1 andalso is_rzero b2
  then (rdiff a1 a2, r0)
  else (rdiff a1 a2, rdiff b1 b2)

(* (a + ib) * (c + id) = (ac - bd, bc + ad) *)
fun cmult (a1,b1) (a2,b2) = 
  if is_rzero b1 andalso is_rzero b2
  then (rmult a1 a2, r0)
  else (rdiff (rmult a1 a2) (rmult b1 b2), 
        raddi (rmult b1 a2) (rmult a1 b2)) 
 
(* (a + ib) / (c + id) = (ac + bd, bc - ad) / c^2+d^2 *) 
fun cdivr (a1,b1) (a2,b2) =
  if is_rzero b1 andalso is_rzero b2
  then (rdivr a1 a2, r0)
  else 
    let val denom = raddi (rmult a2 a2) (rmult b2 b2) in
      (rdivr (raddi (rmult a1 a2) (rmult b1 b2)) denom, 
       rdivr (rdiff (rmult b1 a2) (rmult a1 b2)) denom)
    end
  
fun cdivi (a1,b1) (a2,b2) =
  if is_rzero b1 andalso is_rzero b2
  then (rdivi a1 a2, r0)
  else raise Div
  
fun cmodu (a1,b1) (a2,b2) =
  if is_rzero b1 andalso is_rzero b2
  then (rmodu a1 a2, r0)
  else raise Div

fun crealpart (a1,b1) = (checktimer (); (a1,r0))
fun cimagpart (a1,b1) = (checktimer (); (b1,r0))


end (* struct *)
