structure poly :> poly =
struct

open HolKernel Abbrev boolLib aiLib kernel exec
val ERR = mk_HOL_ERR "poly"

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

exception Norm
val counter = ref 0
val aone = IntInf.fromInt 1
val azero = IntInf.fromInt 0

(* -------------------------------------------------------------------------
   Datatype of polynomials
   ------------------------------------------------------------------------- *)

datatype poly = Poly of ((int * poly list) list * IntInf.int) list
fun dest_poly (Poly x) = x

fun poly_compare (Poly x1, Poly x2) = list_compare mono_compare (x1,x2)
and mono_compare x = cpl_compare vl_compare IntInf.compare x
and vl_compare x = list_compare pins_compare x
and pins_compare x = cpl_compare Int.compare (list_compare poly_compare) x

(* -------------------------------------------------------------------------
   Operations on monomials
   ------------------------------------------------------------------------- *)
 
fun simp_poly poly = filter (fn x => snd x <> azero) poly

fun add_mono l =
  let 
    val d = ref (dempty vl_compare)
    fun f (vl,k) = 
      case dfindo vl (!d) of 
        NONE => (incr counter; d := dadd vl k (!d))
      | SOME kold => 
        let 
          val r = kold + k 
          val _ = incr counter 
        in
          if large_int r then raise Norm else d := dadd vl r (!d)
        end
  in
    app f l;
    simp_poly (dlist (!d))
  end
  
fun mult_mono ((vl1,k1),(vl2,k2)) = 
  let 
    val r = k1 * k2
    val _ = incr counter 
  in
    if large_int r then raise Norm else 
    (dict_sort pins_compare (vl1 @ vl2), r)
  end
  
fun mult_poly l1 l2 = 
  add_mono (map mult_mono (cartesian_product l1 l2))

(* -------------------------------------------------------------------------
   Normalizing polynomials
   ------------------------------------------------------------------------- *)

fun norm ptop = if !counter > 10000 then raise Norm else 
  (
  case ptop of
    Ins (0,[]) => Poly []
  | Ins (1,[]) => Poly [([],IntInf.fromInt 1)]
  | Ins (2,[]) => Poly [([],IntInf.fromInt 2)]
  | Ins (3,[p1,p2]) => 
    let val (l1,l2) = (dest_poly (norm p1), dest_poly (norm p2)) in 
      Poly (add_mono (l1 @ l2))
    end
  | Ins (4,[p1,p2]) => 
    let val (l1,l2) = (dest_poly (norm p1), dest_poly (norm p2)) in  
      Poly (add_mono (l1 @ map_snd (fn x => IntInf.~ x) l2))
    end
  | Ins (5,[p1,p2]) => 
    let 
      val (l1,l2) = (dest_poly (norm p1), dest_poly (norm p2))
      val l3 = mult_poly l1 l2
    in 
      if length l3 > 128 orelse exists large_arb (map snd l3) then 
        let val pins = (5, [Poly l1, Poly l2]) in
          Poly [([pins],aone)]
        end
      else Poly l3
    end
  | Ins (id,pl) => 
    let val pins = (id, map norm pl) in
      Poly [([pins],aone)]
    end
  )
  
fun bare_norm (Ins (id,pl)) = 
  let val pins = (id, map bare_norm pl) in
    Poly [([pins],aone)]
  end

fun normalize p = (counter := 0; 
  norm p handle Norm => bare_norm p)
  
    
end (* struct *)

(* -------------------------------------------------------------------------
   Tests
   ------------------------------------------------------------------------- 
   
load "poly"; load "human"; open aiLib kernel poly human;    
val p = parse_human "( * (+ (% x 2) y) (- x y))";
val py = norm p;   
*)

