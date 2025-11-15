(* ========================================================================= *)
(* Inference rules                                                           *)
(* ========================================================================= *)

structure qrule :> qrule = struct

open aiLib kernel qsyntax
val ERR = mk_HOL_ERR "qrule";

type clause = formula list

(* -------------------------------------------------------------------------
   Int array
   ------------------------------------------------------------------------- *)

val int_glob = Array.array (1000, 0)
val dirtyi = ref ([]: int list)

fun update_int (v,i) = 
  (Array.update (int_glob, ~v, i); dirtyi := v :: !dirtyi)

fun clean_int_glob () =   
  let fun f v = Array.update (int_glob, ~v, 0) in
    app f (!dirtyi); dirtyi := []
  end

fun lookup_int v = Array.sub (int_glob,~v)

(* -------------------------------------------------------------------------
   Bool array
   ------------------------------------------------------------------------- *)

val bool_glob = Array.array (1000, false)
val dirtyb = ref ([]: int list)

fun update_bool v = 
  (Array.update (bool_glob, ~v, true); dirtyb := v :: !dirtyb)

fun clean_bool_glob () =   
  let fun f v = Array.update (bool_glob, ~v, false) in
    app f (!dirtyb); dirtyb := []
  end

fun lookup_bool v = Array.sub (bool_glob,~v)

(* -------------------------------------------------------------------------
   Substition array
   ------------------------------------------------------------------------- *)

val sub_glob = Array.array (1000, NONE: prog option)
val dirtys = ref ([] : int list)

fun update_sub (v,p: prog) = 
  (Array.update (sub_glob, ~v, SOME p); dirtys := v :: !dirtys)

fun clean_sub_glob () =   
  let fun f v = Array.update (sub_glob, ~v, NONE) in
    app f (!dirtys); dirtys := []
  end

fun lookup_sub v = case Array.sub (sub_glob,~v) of 
    NONE => Ins(v,[])
  | SOME p => p

(* -------------------------------------------------------------------------
   Substitution
   ------------------------------------------------------------------------- *)

(* local substitution *)  
fun subst_one (v,p) (Ins (i,pl)) = 
  (
  checktimer ();
  if v = i then p else Ins (i, map (subst_one (v,p)) pl)
  )

fun replace_sub (v,p) =
  let 
    fun f dv = 
      let val dp = valOf (Array.sub (sub_glob,~dv)) in
        Array.update (sub_glob, ~dv, SOME (subst_one (v,p) dp))
      end
  in
    app f (!dirtys)
  end
 
fun elim_var (v,p) = 
  (
  dbg 3 (fn () => "elim: " ^ "x" ^ its (~v) ^ " , " ^ hf p);
  replace_sub (v,p); 
  update_sub (v,p)
  );

fun lookup_sub v = case Array.sub (sub_glob,~v) of 
    NONE => Ins(v,[])
  | SOME p => p
 
fun subst_sub (Ins (i,pl)) = 
  if is_varid i then lookup_sub i else Ins (i, map subst_sub pl);
  
(* -------------------------------------------------------------------------
   Variable renaming
   ------------------------------------------------------------------------- *)

fun store_var (Ins(i,pl)) = 
  (
  if is_varid i then update_bool i else ();
  app (store_var) pl
  )
 
fun available_id counter v = 
  if lookup_bool (!counter) 
  then (decr counter; available_id counter v) 
  else let val r = !counter in decr counter; r end

fun lookup_int_cache counter v = 
  let 
    val n1 = lookup_int v 
    val n2 = if n1 <> 0 then n1 else available_id counter v
  in
    update_int (v,n2); n2
  end

fun rename_var counter (Ins(id,l)) =
  Ins (
      if is_varid id then lookup_int_cache counter id else id, 
      map (rename_var counter) l
      )

fun rename_avoid formula1 formula2 =
  let 
    val _ = store_var formula1
    val r = rename_var (ref (~1)) formula2
  in
    clean_int_glob (); clean_bool_glob (); r
  end    

(* -------------------------------------------------------------------------
   Unification: requires distinct variables   ------------------------------------------------------------------------- *)

fun occur_check v (Ins(i,pl)) = v = i orelse exists (occur_check v) pl;

fun unifyl bindl = 
  case bindl of
    [] => true
  | (p1',p2') :: m => 
    (
    dbg 3 (fn () => "bind: " ^ hf p1' ^ " , " ^ hf p2');
    let 
      val (p1 as Ins(i1,pl1), p2 as Ins(i2,pl2)) = 
        (subst_sub p1', subst_sub p2') 
      val _ = dbg 3 (fn () => "bindr: " ^ hf p1 ^ " , " ^ hf p2)
    in 
      case (is_varid i1, is_varid i2) of
        (true,true) => 
        (if i1 <> i2 then elim_var (i1,p2) else (); unifyl m)
      | (true,false) =>
        if occur_check i1 p2 then false else (elim_var (i1,p2); unifyl m)
      | (false,true) =>
        if occur_check i2 p1 then false else (elim_var (i2,p1); unifyl m)
      | (false,false) => 
        if i1 <> i2 orelse length pl1 <> length pl2 then false
        else unifyl (combine (pl1,pl2) @ m)
    end
    )
    
fun unify (p1,p2) = 
  (
  clean_sub_glob ();
  dbg 2 (fn () => "unify: " ^ hf p1 ^ " , " ^ hf p2); 
  let val b = unifyl [(p1,rename_avoid p1 p2)] in
    dbg 2 (fn () => "unify: " ^ (if b then "yes" else "no"));
    b
  end
  )

(* 
load "qsubst"; open aiLib qsyntax qsubst;
val f1 = fh "(+ x1 0)";
val f2 = fh "(+ 0 0)";
dbg_flag := true;
val b = unify (f1,f2);
*)

(* -------------------------------------------------------------------------
   Instantiation rule (with respect to sub_glob) 
   ------------------------------------------------------------------------- *)

fun inst_aux (p as (Ins(i,pl))) =
  (
  checktimer ();
  if is_varid i then 
    case Array.sub (sub_glob, ~i) of
      NONE => p
    | SOME newp => newp
  else Ins(i, map inst_aux pl)
  )

(* -------------------------------------------------------------------------
   Paramodulation
   ------------------------------------------------------------------------- *)

fun replace_nth n l f = 
  case l of
    [] => raise ERR "replace_nth" ""
  | a :: m => if n <= 0 then f a :: m else replace_nth (n-1) m f

fun insert_posl pose m instm tml = replace_nth pose tml (insert_pos m instm)

and insert_pos pos instm (Ins (i,tml)) = 
  (
  checktimer ();
  (
  case pos of
    [] => instm
  | pose :: m => Ins (i, insert_posl pose m instm tml)
  )
  )
  
fun rwl redex iref pos pltop =
  (
  checktimer ();
  let fun loop i pl = case pl of [] => NONE | p :: m => 
    (
    case rw redex iref (i :: pos) p of 
      NONE => loop (i+1) m
    | SOME pos => SOME pos
    )
  in
    loop 0 pltop
  end
  )
  
and rw redex iref pos (p as Ins(i,pl)) =
  if not (unify (redex,p)) then rwl redex iref pos pl else
  (decr iref; if !iref < 0 then SOME (rev pos) else rwl redex iref pos pl)

fun paramodulate condl eq (pl,i) = case rwl (fst eq) (ref i) [] pl of
    SOME (pose :: m) => 
      SOME (
        insert_posl pose m (inst_aux (snd eq)) (map inst_aux pl) @
        map inst_aux condl)
  | _ => NONE

(* -------------------------------------------------------------------------
   Resolution
   ------------------------------------------------------------------------- *)

local

fun llfinda iref a l2 = case l2 of [] => NONE | a2 :: m2 => 
  if not (unify (a,neg a2)) then llfinda iref a m2 else
  (decr iref; if !iref < 0 then SOME (a,a2) else llfinda iref a m2)

fun llfind iref l1 l2 = case l1 of [] => NONE | a1 :: m1 => 
  (case llfinda iref a1 l2 of NONE => llfind iref m1 l2 | x => x)

in

fun resolve pl1 (pl2,i2) = case llfind (ref i2) pl1 pl2 of 
   SOME (a,b) => SOME (map inst_aux (pl1 @ pl2))
 | NONE => NONE   


end (* local *)


(* -------------------------------------------------------------------------
   Factoring
   ------------------------------------------------------------------------- *)

fun factor_set pl = mk_sameorder_set timed_formula_compare pl

local

fun llfinda iref a l2 = case l2 of [] => NONE | a2 :: m2 => 
  if not (unify (a,a2)) then llfinda iref a m2 else
  (decr iref; if !iref < 0 then SOME (a,a2) else llfinda iref a m2)

fun llfind iref l1 l2 = case l1 of [] => NONE | a1 :: m1 => 
  (case llfinda iref a1 l2 of NONE => llfind iref m1 l2 | x => x)

in

fun factor (pl,i) = case llfind (ref i) pl pl of 
    SOME (a,b) => SOME (map inst_aux pl)
  | NONE => NONE 
    
end (* local *)
  
(* -------------------------------------------------------------------------
   Removing conflicting literals and disequalities of ssame term
   ------------------------------------------------------------------------- *)

fun remove_conflict pl =
  let 
    val d = enew timed_formula_compare pl
    fun f x = not (emem (neg x) d)
  in
    filter f pl
  end

fun is_ineq p = case p of
    Ins(0,[Ins(3,[p1,p2])]) => timed_formula_compare (p1,p2) = EQUAL
  | _ => false

fun remove_diseq pl = filter (not o is_ineq) pl


end (* struct *)
