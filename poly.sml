structure poly :> poly =
struct

open HolKernel Abbrev boolLib aiLib kernel execarb
val ERR = mk_HOL_ERR "poly"

(* -------------------------------------------------------------------------
   Datatype of polynomials
   ------------------------------------------------------------------------- *)

datatype poly = 
    Pins of int * poly list
  | Poly of Arbint.int * (poly list * Arbint.int) list

fun dest_poly poly = case Poly x => x | _ => raise ERR "poly" "" 

fun poly_compare (py1,py2) = case (py1,py2) of
    (Pins pi1, Pins pi2) => cpl_compare Int.compare poly_compare (pi1,pi2)
  | (Pins _, _) => LESS
  | (_, Pins _) => GREATER
  | (Poly x1, Poly x2) => cpl_compare Arbint.compare mono_compare (x1,x2) 
and mono_compare = list_compare (cpl_compare vl_compare Arbint.compare)
and vl_compare = list_compare poly_compare
 
(* -------------------------------------------------------------------------
   Operations on monomials
   ------------------------------------------------------------------------- *)
 
fun add_mono l =
  let 
    val d = ref (dempty vl_compare)
    fun f (vl,k) = 
      case dfindo vl (!d) of 
        NONE => d := dadd vl k (!d)
      | SOME kold => d := dadd vl (Arbint.+ (kold,k)) (!d) 
  in
    app f l;
    dlist (!d)
  end

fun diff_mono l1 l2 =
  let 
    val d = ref (dnew (list_compare poly_compare) l1) 
    fun f (vl,k) = 
      case dfindo vl (!d) of 
        NONE => d := dadd vl k (!d)
      | SOME kold => d := dadd vl (Arbint.- (kold,k)) (!d) 
  in
    app f l2;
    dlist (!d)
  end
  
fun mult_mono_aux (vl1,k1) (vl2,k2) = 
  (dict_sort poly_compare (vl1 @ vl2) , Arbint.* (k1,k2)) 
  
fun mult_mono l1 l2 = 
  add_mono (map mult_mono_aux (cartesian_product l1 l2))

(* -------------------------------------------------------------------------
   Normalizing polynomials
   ------------------------------------------------------------------------- *)

fun norm ptop = case ptop of
    Ins (0,[]) => Poly (Arbint.fromInt 0,[])
  | Ins (1,[]) => Poly (Arbint.fromInt 1,[])
  | Ins (2,[]) => Poly (Arbint.fromInt 2,[])
  | Ins (3,[p1,p2]) => 
    let val ((c1,l1),(c2,l2)) = (dest_poly (norm p1), dest_poly (norm p2)) in 
      Poly (Arbint.+ (c1,c2), add_mono (l1 @ l2))
    end
  | Ins (4,[p1,p2]) => 
    let val ((c1,l1),(c2,l2)) = (dest_poly (norm p1), dest_poly (norm p2)) in 
      Poly (Arbint.- (c1,c2), diff_mono l1 l2)
    end
  | Ins (5,[p1,p2]) => 
    let val ((c1,l1),(c2,l2)) = (dest_poly (norm p1), dest_poly (norm p2)) in 
      val c3 = Arbint.* (c1,c2)
      val l3 = mult_mono l1 l2
    in 
      if large_arb c3 orelse length l3 > 128 orelse 
         exists large_arb (map snd l3) 
      then 
        let val pins = Pins (5, [Poly (c1,l1), Poly (c2,l2)]) in
          Poly (Arbint.zero,[([pins],Arbint.one)])
        end
      else Poly (c3,l3)
    end
  | Ins (id,pl) => 
    let val pins = Pins (id, map norm pl) in
      Poly (Arbint.zero,[([pins],Arbint.one)])
    end
    
end (* struct *)

(* -------------------------------------------------------------------------
   Examples
   ------------------------------------------------------------------------- 
   
load "poly"; load "human"; open aiLib kernel poly human;    
   
   
   
   
   
   
   
   
*)

