
load "kernel"; open aiLib kernel;

(*
## variable are nonpositive integers
## constants are positive integers

### term primitives
dest_ins tml 
mk_ins tml
term_eq tml1 tml2
term_comp 
is_inst tm1 tm2
subst tm1 tm2 tm3


### theorem primitives
rewrite thm1 thm2
rewritel thml1 thm2
*)

(* uses the global substa array *)


fun all2 f l1 l2 = case (l1,l2) of
    ([],[]) => true
  | (a1 :: m1, a2 :: m2) => f a1 a2 andalso all2 f m1 m2
  | _ => false

(* creating applying substitution *)
val substa = Array.array (128, NONE)
val dirty = ref ([] : int list)

fun inst_term (p as (Ins(i,pl))) =
  if i < 0 then 
    case Array.sub (substa, ~i) of
      NONE => p
    | SOME newp => newp
  else Ins(i,map inst_term pl)

fun update_substa i term =
  (Array.update (substa, i, SOME term); dirty := i :: !dirty)

(* match term *)
fun match_term_aux (p1 as Ins(i1,pl1)) (p2 as Ins(i2,pl2)) =
  if i1 < 0 then 
    (
    case Array.sub (substa, ~i1) of
      NONE => (update_substa (~i1) p2; true)
    | SOME p => prog_compare (p,p2) = EQUAL
    )
  else if i1 = i2 then all2 match_term_aux pl1 pl2
  else false
  
fun match_term p1 p2 =
  let 
    val _ = dirty := []
    val b = match_term_aux p1 p2
  in
    if b then SOME (!dirty) else NONE
  end;
    
val r = match_term (Ins(2,[])) (Ins(0,[]));

