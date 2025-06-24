(* ========================================================================= *)
(* DESCRIPTION   : Extended program datatype to store names for subloops     *)
(* ========================================================================= *)

structure qsubst :> qsubst = struct

open aiLib kernel;
val ERR = mk_HOL_ERR "qsubst";

type prog = kernel.prog

(* load "qsubst"; open aiLib kernel qsubst; *)


(* -------------------------------------------------------------------------
   Global array substitution (* todo: catch Subscript error *)
   ------------------------------------------------------------------------- *)

val sub_glob = Array.array (1000, NONE: prog option)
val dirty = ref ([] : int list)

fun clean_sub_glob () =   
  let fun f dv = Array.update (sub_glob, ~dv, NONE) in
    app f (!dirty); dirty := []
  end

(* -------------------------------------------------------------------------
   Substitutions   
   ------------------------------------------------------------------------- *)

fun is_var id = id < 0

(* local substitution *)  
fun subst_one (v,p) (Ins (i,pl)) = 
  if v = i then p else Ins (i, map (subst_one (v,p)) pl);

fun update_sub (v,p: prog) = 
  (Array.update (sub_glob, ~v, SOME p); dirty := v :: !dirty)

fun replace_sub (v,p) =
  let 
    fun f dv = 
      let val dp = valOf (Array.sub (sub_glob,~dv)) in
        Array.update (sub_glob, ~dv, SOME (subst_one (v,p) dp))
      end
  in
    app f (!dirty)
  end
 
fun elim_var (v,p) = (replace_sub (v,p); update_sub (v,p: prog));

fun lookup_sub v = case Array.sub (sub_glob,~v) of 
    NONE => Ins(v,[])
  | SOME p => p
 
fun subst_sub (Ins (i,pl)) = 
  if is_var i then lookup_sub i else Ins (i, map subst_sub pl);

(* -------------------------------------------------------------------------
   Matching (with respect to sub_glob)
   ------------------------------------------------------------------------- *)

fun match (p1 as Ins(i1,pl1), p2 as Ins(i2,pl2)) =
  if is_var i1 then 
    (
    case Array.sub (sub_glob, ~i1) of
      NONE => (update_sub (i1,p2); true)
    | SOME p => prog_compare (p,p2) = EQUAL
    )
  else 
    if i1 <> i2 orelse length pl1 <> length pl2 
    then false
    else all match (combine (pl1,pl2))
  
(* -------------------------------------------------------------------------
   Unification
   ------------------------------------------------------------------------- *)
   
fun occur_check v (Ins(i,pl)) = v = i orelse exists (occur_check v) pl;

fun unifyl bindl = case bindl of
    [] => SOME (!dirty)
  | (p1',p2') :: m => 
    let val (p1 as Ins(i1,pl1), p2 as Ins(i2,pl2)) = 
      (subst_sub p1', subst_sub p2') 
    in 
      case (is_var i1, is_var i2) of
        (true,true) => 
        (if i1 <> i2 then elim_var (i1,p2) else (); unifyl m)
      | (true,false) =>
        if occur_check i1 p2 then NONE else (elim_var (i1,p2); unifyl m)
      | (false,true) =>
        if occur_check i2 p1 then NONE else (elim_var (i2,p1); unifyl m)
      | (false,false) => 
        if i1 <> i2 orelse length pl1 <> length pl2 
        then NONE 
        else unifyl (combine (pl1,pl2) @ m)
    end;
  
fun unify p1 p2 = unifyl [(p1,p2)];

(* -------------------------------------------------------------------------
   Instantiation rule (with respect to sub_glob) 
   ------------------------------------------------------------------------- *)

fun with_match (p1,p2) f =
  let 
    val b = match (p1,p2)
    val r = f b
    val _ = clean_sub_glob ()
  in
    r
  end

fun inst_match_aux (p as (Ins(i,pl))) =
  if is_var i then 
    case Array.sub (sub_glob, ~i) of
      NONE => p
    | SOME newp => newp
  else Ins(i, map inst_match_aux pl)
  
fun inst_match (p1,p2) p =
  let fun f b = if b then inst_match_aux p else p in
    with_match (p1,p2) f
  end
  
(* -------------------------------------------------------------------------
   Rewrite rule (with respect to sub_glob)
   ------------------------------------------------------------------------- *)
  
val eqi = 20 (* todo changes to reflect the number for equality *)
fun is_eq (Ins(i,pl)) = i = eqi
fun dest_eq (Ins(i,pl)) = pair_of_list pl 
 
fun rewrite_match_one (p1,p2) (p as (Ins(i,pl))) =
  let fun f b = if b then inst_match_aux p2 else p in
    with_match (p1,p) f
  end
  
fun rewrite_match_aux eqpair (p as (Ins(i,pl))) =
  let val newp = Ins(i, map (rewrite_match_aux eqpair) pl) in
    rewrite_match_one eqpair newp
  end

fun rewrite_match (eq,p) = 
  if not (is_eq eq) then p else rewrite_match_aux (dest_eq eq) p

(* -------------------------------------------------------------------------
   Modus ponens with match
   ------------------------------------------------------------------------- *) 

val impi = 21 (* todo changes to reflect the number for equality *)
fun is_imp (Ins(i,pl)) = i = impi
fun dest_imp (Ins(i,pl)) = pair_of_list pl 

fun mp_match_aux (p1,p2) p =
  let fun f b = if b then inst_match_aux p2 else p in
    with_match (p1,p) f
  end

fun mp_match (imp,p) =
  if not (is_imp imp) then p else mp_match_aux (dest_imp imp) p






end (* struct *)
