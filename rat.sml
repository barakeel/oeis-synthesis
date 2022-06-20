structure rat :> rat =
struct

type rat = (Arbint.int * Arbint.int)

local open Arbint in

fun arb_pow a b = if b <= zero then one else a * arb_pow a (b-one)
val maxarb = arb_pow (fromInt 10) (fromInt 285) (* 4.685 * 10 ^ 284 *)
val minarb = ~maxarb
val maxint = arb_pow (fromInt 2) (fromInt 64)
val minint = ~maxint
fun large_arb x = x > maxarb orelse x < minarb
fun large_int x = x > maxint orelse x < minint
fun large_rarb (x,y) = large_arb x orelse large_arb y
fun large_rint (x,y) = large_int x orelse large_int y
fun gcd_aux a b =
  if b = zero then a else gcd_aux b (a mod b)
fun gcd a b = 
  let 
    val (a',b') = (if a < zero then ~a else a, if b < zero then ~b else b)
    val (a'',b'') = if a' < b' then (b',a') else (a',b')
  in
    gcd_aux a'' b''
  end
fun reduce (a,b) = 
  if b = one then (a,b) else
  let 
    val (a',b') = if b < zero then (~a, ~b) else (a,b)
    val r = gcd a' b' 
  in 
    (a' div r, b' div r) 
  end
val rzero = (zero,one);
val rone = (one,one);
val rtwo = (two,one);
fun rmult ((a1,b1),(a2,b2)) = reduce (a1 * a2, b1 * b2)
fun raddi ((a1,b1),(a2,b2)) = reduce (a1 * b2 + a2 * b1, b1 * b2) 
fun rdiff ((a1,b1),(a2,b2)) = reduce (a1 * b2 - a2 * b1, b1 * b2)   
fun rmodu ((a1,b1),(a2,b2)) = reduce ((a1 * b2) mod (a2 * b1), b1 * b2)
fun rcond ((a,b),c,d) = if a <= zero then c else d
fun rcondeq ((a,b),c,d) = if a = zero then c else d
fun rdivi ((a1,b1),(a2,b2)) = ((a1 * b2) div (b1 * a2),one) 
fun rdivr ((a1,b1),(a2,b2)) = reduce (a1 * b2, b1 * a2)
fun rintpart (a1,b1) = (a1 div b1, one)
fun rnumer (a1,b1) = (a1,one)
fun rdenom (a1,b1) = (b1,one)
fun is_rint (a1,b1) = (b1 = one)
fun intpart (a1,b1) = a1 div b1
fun mk_rat a1 = (a1,one)

end

end
