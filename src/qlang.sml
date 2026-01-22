(* ========================================================================= *)
(* Language for the Qprover                                                  *)
(* ========================================================================= *)

structure qlang :> qlang = struct

open HolKernel Abbrev boolLib aiLib kernel qsyntax qrule sexp
val ERR = mk_HOL_ERR "qlang"

type formula = qsyntax.formula
type qprove = (formula list * (prog * int))
type state = prog list
type exec = state * state -> state
type goal = formula list * formula
type tactic = goal list -> goal list

exception Error
exception Proof
fun error () = raise Error

(* -------------------------------------------------------------------------
   Objects
   ------------------------------------------------------------------------- *)

datatype obje = Thm of formula list * int | Term of formula
type obj = obje list

fun is_thm obje = case obje of Thm _ => true | _ => false
fun mk_thmobj tml = [Thm (tml,0)];
fun dest_thmobj thm = case thm of
    Thm (clause,_) :: _ => clause
  | _ => raise ERR "dest_thmobj" "";

fun size_obje x = case x of
    Thm (tml,_) => sum_int (map formula_size tml)
  | Term tm => formula_size tm

fun size_obj x = sum_int (map size_obje x)

fun hfobje x = case x of
   Thm (c,n) => (* "Thm " ^ hfc c ^ " @ " ^ its n *) hfc c
 | Term t => "Term " ^ hf t

fun hfobj obj = String.concatWith ", " (map hfobje obj);

val see = pe o hfobj

fun is_proof f (thml1,thml2) = (f (thml1,thml2); false) handle Proof => true

fun mk_thm tml = Thm (tml,0)
fun dest_thm thm = case thm of
    Thm (clause,_) => clause
  | _ => raise ERR "dest_thm" ""

(* -------------------------------------------------------------------------
   Axioms
   ------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------
   Simplify and check if the proof is finished
   ------------------------------------------------------------------------- *)

fun simp clause =
  let val r = remove_diseq (remove_conflict (factor_set clause)) in
    if null r then raise Proof else r
  end

(* -------------------------------------------------------------------------
   Moving index
   ------------------------------------------------------------------------- *)

fun next_obj obj =
  case obj of
    Thm (x,i) :: m => Thm (x,i+1) :: m
  | _ => error ()

(* -------------------------------------------------------------------------
   Paramodulate
   ------------------------------------------------------------------------- *)

fun find_nth acc test n l = case l of
    [] => NONE
  | a :: m =>
    if not (test a) then find_nth (a :: acc) test n m else
    if n <= 0 then SOME (a,rev acc @ m) else find_nth (a :: acc) test (n-1) m

fun paramodulate_obj obj1 obj2 =
  case (obj1,obj2) of
    (Thm (clause1,i1) :: _, Thm(clause2,i2) :: m2) =>
    (
    case find_nth [] is_eq i1 clause1 of
      SOME (A ((0,3),[red,res]),clause1') =>
      (
      dbg 2 (fn () => "rw: " ^ hf red ^ " , " ^ hf res);
      case paramodulate clause1' (red,res) (clause2,i2) of
        SOME newclause =>
        let val r = simp newclause in
          dbg 1 (fn () => "rw: " ^ hfc r);
          Thm (r, 0) :: m2
        end
      | NONE =>
        (
        dbg 1 (fn () => "rw: identity");
        obj2
        )
      )
      | _ => error ()
    )
  | _ => error ()

(* -------------------------------------------------------------------------
   Resolve
   ------------------------------------------------------------------------- *)

fun resolve_obj obj1 obj2 = case (obj1,obj2) of
    (Thm (clause1,_) :: _, Thm thm2 :: m2) =>
    (
    case resolve clause1 thm2 of
      SOME newclause => Thm (simp newclause, 0) :: m2
    | NONE => obj2
    )
  | _ => error ()

(* -------------------------------------------------------------------------
   Factor
   -------------------------------------------------------------------------*)

fun factor_obj obj = case obj of
    Thm thm :: m =>
    (case factor thm of NONE => obj | SOME newclause =>
     Thm (simp newclause, 0) :: m)
  | _ => error ()

(* -------------------------------------------------------------------------
   Control flow
   ------------------------------------------------------------------------- *)

fun varx (x,y) = x

fun vary (x,y) = y

fun cond x f1 f2 = if null x then f2 () else f1 ()

fun while2 f g x y =
  if null x then y else while2 f g (f (x,y)) (g (x,y))

fun eq_obj x y =
  if PolyML.pointerEq (x,y) then y else
  (
  case (x,y) of
    (Thm (thm1,_) :: _, Thm (thm2,_) :: _)  =>
    if list_compare formula_compare (thm1,thm2) = EQUAL then y else []
  | (Term t1 :: _ , Term t2 :: _) =>
    if formula_compare (t1,t2) = EQUAL then y else []
  | _ => []
  )

(* -------------------------------------------------------------------------
   List operations
   ------------------------------------------------------------------------- *)

fun hd_obj a = case a of e :: m => [e] | _ => error ()
fun tl_obj a = case a of e :: m => m | _ => error ()
fun push_obj a b = (checktimern (length a); a @ b)
val null_obj = []

(* -------------------------------------------------------------------------
   Term operations
   ------------------------------------------------------------------------- *)

fun same_id x y = case (x,y) of
     (Thm _ :: _, Thm _ :: _)  => y
   | (Term (A (i1,_)) :: _ , Term (A (i2,_)) :: _ ) =>
     if i1 = i2 then y else []
   | _ => []

fun is_var x = case x of
    Term (A(i,_)) :: _ => if is_varid i then x else []
  | _ => []

fun is_not x = case x of
    Term (A(i,_)) :: _ => if i = not_id then x else []
  | _ => []

fun is_eq x = case x of
    Term (A(i,_)) :: _ => if i = eq_id then x else []
  | _ => []

fun is_add x = case x of
    Term (A(i,_)) :: _ => if i = add_id then x else []
  | _ => []

fun dest x = case x of
    Thm (tml,_) :: m => map Term tml @ m
  | Term (A(_,tml)) :: m => map Term tml @ m
  | [] => error ()

(* -------------------------------------------------------------------------
   Induction
   ------------------------------------------------------------------------- *)

(* looks for skolems with no arguments *)
fun nth_skoleml n skd pl = case pl of [] => NONE | p :: m =>
  (
  case nth_skolem n skd p of
     SOME id => SOME id
   | NONE => nth_skoleml n skd m
  )

and nth_skolem n skd (A(id,pl)) =
  if is_skolemid id andalso null pl then
    if emem id (!skd) then nth_skoleml n skd pl else
    if elength (!skd) >= n then SOME id else
    (skd := eadd id (!skd); nth_skoleml n skd pl)
  else nth_skoleml n skd pl

fun nth_skoleml n skd pl = case pl of [] => NONE | p :: m =>
  (
  case nth_skolem n skd p of
     SOME id => SOME id
   | NONE => nth_skoleml n skd m
  )

fun nth_skolem_thml n skd thml = case thml of [] => NONE | thm :: m =>
  (
  case nth_skoleml n skd (dest_thm thm) of
    NONE => nth_skolem_thml n skd m
  | SOME id => SOME id
  )

fun subst_one_litl (id,tm) litl = map (subst_one (id,tm)) litl
fun subst_one_thm (id,tm) thm = Thm (subst_one_litl (id,tm) (dest_thm thm), 0)

fun negate_thml thml =
  let
    val clausel1 = map (map neg o dest_thm) thml
    val clausel2 = cartesian_productl clausel1
  in
    map mk_thm clausel2
  end

fun induct_obj f obj =
  let
    val _ = dbg 1 (fn () => "induction: " ^ hfobj obj)
    val thml = filter is_thm obj
    val n = case thml of Thm (_,n) :: _ => n | _ => error ()
    val skold = case nth_skolem_thml n (ref (eempty id_compare)) thml of
      NONE => error ()
    | SOME x => x
    val zero = A((1,0),[])
    val p0 = map (subst_one_thm (skold,zero)) thml
    val _ = dbg 2 (fn () => "base case: " ^ hfobj p0)
    val sk = A(fresh_skolemid (),[])
    val psk = map (subst_one_thm (skold,sk)) thml
    val _ = dbg 2 (fn () => "inductive hypothesis: " ^ hfobj psk)
    val pssk = negate_thml (map (subst_one_thm (skold, mk_add (sk,one))) thml)
    val _ = dbg 2 (fn () => "inductive consequent: " ^ hfobj pssk)
  in
    if is_proof f (p0,[]) then pssk @ psk else error ()
  end

fun induct_obji obj =
  let
    val _ = dbg 1 (fn () => "induction: " ^ hfobj obj)
    val thml = filter is_thm obj
    val n = case thml of Thm (_,n) :: _ => n | _ => error ()
    val skold = case nth_skolem_thml n (ref (eempty id_compare)) thml of
      NONE => error ()
    | SOME x => x
    val zero = A((1,0),[])
    val p0 = map (subst_one_thm (skold,zero)) thml
    val _ = dbg 2 (fn () => "base case: " ^ hfobj p0)
    val sk = A(fresh_skolemid (),[])
    val psk = negate_thml (map (subst_one_thm (skold,sk)) thml)
    val _ = dbg 2 (fn () => "inductive hypothesis: " ^ hfobj psk)
    val pssk = map (subst_one_thm (skold, mk_add (sk,one))) thml
    val _ = dbg 2 (fn () => "inductive consequent: " ^ hfobj pssk)
  in
    (p0, pssk @ psk)
  end

(* -------------------------------------------------------------------------
   Conjecturing
   ------------------------------------------------------------------------- *)

fun conjecture_obj f thm = case thm of
    Term tm :: m =>
    (
    if not (is_boolean tm) then error () else
    let
      val _ = dbg 1 (fn () => "conjecture: " ^ hf tm)
      val obj = map mk_thm (CNF (neg tm))
    in
      if is_proof f (obj,[]) then obj @ m else error ()
    end
    )
  | _ => error ()

(* -------------------------------------------------------------------------
   Polynomial normalization
   ------------------------------------------------------------------------- *)

fun add_poly (p1,p2) =
  (
  checktimer ();
  case (p1,p2) of
    ([], p) => p
  | (p, []) => p
  | ((m1,c1) :: ms1, (m2,c2):: ms2) =>
    (
    case list_compare formula_compare (m1,m2) of
      EQUAL =>
      let val c = c1 + c2 in
        if c = 0 then add_poly (ms1, ms2)
        else (m1, c) :: add_poly (ms1, ms2)
      end
    | LESS => (m1, c1) :: add_poly (ms1, p2)
    | GREATER => (m2, c2) :: add_poly (p1, ms2)
    )
  )

fun min_poly p = map (fn (a,b) => (a,~b)) p

fun diff_poly (p1,p2) = add_poly (p1, min_poly p2)


fun merge_mono l1 l2 =
  (
  checktimer ();
  case (l1,l2) of
     (l, []) => l
  | ([], l) => l
  | (a1 :: m1, a2 :: m2) =>
    (
    case formula_compare (a1,a2) of
      EQUAL => a1 :: a2 :: merge_mono m1 m2
    | LESS => a1 :: merge_mono m1 l2
    | GREATER => a2 :: merge_mono l1 m2
    )
  )

fun mult_mono (m1,c1) (m2,c2) = (merge_mono m1 m2, c1 * c2)

fun mult_mono_poly m p = map (mult_mono m) p;

fun mult_poly (p1,p2) = case p1 of
    [] => []
  | m :: ms => add_poly (mult_mono_poly m p2, mult_poly (ms,p2));

(* todo normalize inner part first *)

fun formula_to_poly p = case p of
    A ((0,3),[p1,p2]) => add_poly (formula_to_poly p1, formula_to_poly p2)
  | A ((0,4),[p1,p2]) => diff_poly (formula_to_poly p1, formula_to_poly p2)
  | A ((0,5),[p1,p2]) => mult_poly (formula_to_poly p1, formula_to_poly p2)
  | A ((1,x),[]) => [([],x)]
  | _ => [([p],1)];


fun mono_to_formula1 xl = case xl of
    [] => raise ERR "mono_to_formula1" ""
  | [x] => x
  | x :: m => A (mult_id, [x, mono_to_formula1 m])

fun mono_to_formulac (xl,coeff) = case xl of
    [] => A ((1,coeff),[])
  | x :: m => A (mult_id, [x, mono_to_formulac (m,coeff)])

fun mono_to_formula (xl,coeff) =
  if coeff = 1
  then (if null xl then one else mono_to_formula1 xl)
  else mono_to_formulac (xl,coeff)

fun poly_to_formula poly = case poly of
    [] => zero
  | [mono] => mono_to_formula mono
  | mono :: m => A (add_id, [mono_to_formula mono, poly_to_formula m])

fun norm_poly_one formula = poly_to_formula
  (filter (fn x => snd x <> 0) (formula_to_poly formula))

fun norm_poly (A(id,argl)) =
  if id = add_id orelse id = mult_id orelse id = diff_id
  then norm_poly_one (A(id, map norm_poly_done argl))
  else A(id, map norm_poly argl)

and norm_poly_done (A(id,argl)) =
  if id = add_id orelse id = mult_id
  then A(id, map norm_poly_done argl)
  else A(id, map norm_poly argl)

fun norm_poly_obj obj =
  (
  dbg 1 (fn () => "norm: " ^ hfobj obj);
  case obj of
    Thm (clause,_) :: m => Thm (simp (map norm_poly clause), 0) :: m
  | _ => error ()
  )
  
  

(* -------------------------------------------------------------------------
   Unfolding loops
   ------------------------------------------------------------------------- *)

(* todo: add check for strictly bigger than 0 *)

val xid = (3,0)
val yid = (3,1)
val x_flag = ref false (* remove this flag eventually *)

fun replace_atl f p = case p of
    A ((0,9),_) => f p
  | A ((0,13),_) => f p
  | A ((0,16),_) => f p
  | A (i,pl) => A (i,map (replace_atl f) pl)

fun is_geq0 l = case l of
    [] => true
  | A ((1,i),[]) :: m => if i >= 0 then is_geq0 m else false
  | A (id,pl) :: m =>
    if id = xid andalso !x_flag then is_geq0 m else
    if mem id [add_id, mult_id, div_id, mod_id] then is_geq0 (pl @ m)
    else false

fun is_greater0 p = is_geq0 [norm_poly (mk_diff (p,one))]

fun is_leq0 p = is_geq0 [norm_poly (mk_diff (zero,p))]

fun unfold_one p = case p of
    A ((0,9),[pa,pb,pc]) =>
    if is_greater0 pb then
      let
        val xrep = A ((0,9),[pa, mk_diff (pb,one), pc])
        val yrep = pb
      in
        substl [(xid,xrep),(yid,yrep)] pa
      end
    else if is_leq0 pb then pc
    else raise ERR "unfold_one" ("bound: " ^ hf pb)
  | A (id,[pa,pb,pc,pd,pe]) =>
    if not (mem id [(0,13),(0,16)])
      then raise ERR "unfold_one" "not a loop"
    else if is_greater0 pc then
      let
        val pc' = mk_diff (pc,one)
        val xrep = A ((0,13),[pa,pb,pc',pd,pe])
        val yrep = A ((0,16),[pa,pb,pc',pd,pe])
      in
        substl [(xid,xrep),(yid,yrep)] (if id = (0,13) then pa else pb)
      end
    else if is_leq0 pc then (if id = (0,13) then pd else pe)
    else raise ERR "unfold_one" ("bound: " ^ hf pc)
  | _ => raise ERR "unfold_one" "not a loop"

fun unfold p = replace_atl unfold_one p;

fun unfold_num_one p = case p of
    A ((0,9),[pa,pb,pc]) =>
    let val pb' = eval pb in
      if not (is_num pb') then p else
      if is_greater0 pb then
        let
          val xrep = A ((0,9),[pa, mk_diff (pb',one), pc])
          val yrep = pb
        in
          substl [(xid,xrep),(yid,yrep)] pa
        end
      else if is_leq0 pb then pc
      else raise ERR "unfold_num_one" ("bound: " ^ hf pb)
    end
  | A (id,[pa,pb,pc,pd,pe]) =>
    let val pc' = eval pc in
      if not (is_num pc') then p else
      if not (mem id [(0,13),(0,16)])
        then raise ERR "unfold_num_one" "not a loop"
      else if is_greater0 pc' then
        let
          val pc'' = mk_diff (pc',one)
          val xrep = A ((0,13),[pa,pb,pc'',pd,pe])
          val yrep = A ((0,16),[pa,pb,pc'',pd,pe])
        in
          substl [(xid,xrep),(yid,yrep)] (if id = (0,13) then pa else pb)
        end
      else if is_leq0 pc' then (if id = (0,13) then pd else pe)
      else raise ERR "unfold_num_one" ("bound: " ^ hf pc)
    end
  | _ => raise ERR "unfold_num_one" "not a loop"

fun unfold_num p = replace_atl unfold_num_one p;

val x0id = (3,0)
val x1 = A((3,1),[])

fun decouple_one v p =  case p of
    A ((0,9),[pa,pb,pc]) =>
    let val pc' = subst_one (x0id,v) pc in
      A ((0,9),[pa,pb,pc'])
    end
  | A (id,[pa,pb,pc,pd,pe]) =>
    if not (mem id [(0,13),(0,16)])
      then raise ERR "decouple_loop" "not a loop"
    else
    let
      val pd' = subst_one (x0id,v) pd
      val pe' = subst_one (x0id,v) pe
    in
      A (id,[pa,pb,pc,pd',pe'])
    end
  | _ => raise ERR "decouple_loop" "not a loop"

fun decouple p =
  let val v = fresh_var () in replace_atl (decouple_one v) p end


(* -------------------------------------------------------------------------
   Parsing the conjecture
   ------------------------------------------------------------------------- *)

fun rename sexp = case sexp of
    Atom "*" => Atom "."
  | Atom "x" => Atom "x0"
  | Atom x => Atom x
  | Sexp l => Sexp (map rename l);

fun find_body e = case e of
    Sexp [Atom "assert",Sexp [Atom "forall",_,Sexp [Atom "=",_,body]]]
     => SOME body
  | _ => NONE;

fun conjecture_of dir pbs =
  let
    val l1 = smt_hol.read_smt_sexp (dir ^ "/" ^ pbs);
    val l2 = List.mapPartial find_body l1;
    val (s1,s2) = pair_of_list (map (sexp_to_string o rename) l2)
  in
    "(forall x0 (= " ^ s1 ^ " "  ^ s2 ^ "))"
  end
  handle HOL_ERR {message = s, ...} => raise (ERR pbs s);

val posx0 = mk_geq (mk_var 0, zero)

fun get_problems () =
  let
    fun contain l (Ins(id,argl)) = mem id l orelse exists (contain l) argl;
    fun contain_app l (a,(p1,p2)) = contain l p1 orelse contain l p2
    val appl = smt_progx.read_anumprogpairs
      (selfdir ^ "/smt_benchmark_progpairs")
    val avoidl = [4,6,7,8,12];
    val (appl1,appl2) = partition (contain_app avoidl) appl;
    val avoidl = [13,14];
    val (appl2a,appl2b) = partition (contain_app avoidl) appl2;
    fun pplen (a,(p1,p2)) = prog_size p1 + prog_size p2;
    val appl3 = dict_sort compare_imin (map_assoc pplen appl2a);
    fun f ((a,(p1,p2)),n) =
      (a, [([posx0], mk_eq (prog_to_formula p1, prog_to_formula p2))])
  in
    map f appl3
  end

(* -------------------------------------------------------------------------
   Induction and reasoning over equality between programs
   ------------------------------------------------------------------------- *)

type eq = formula * formula

fun pairmap f (x1,x2) = (f x1, f x2);
fun pairfst f (x1,x2) = (f x1, x2);
val xid = (3,0);
val xplusone = mk_add (mk_var 0, one);
val xplustwo = mk_add (mk_var 0, A ((1,2),[]));

fun base_case x = pairmap (subst_one (xid,zero)) x;

fun rep_id bref (oldid,newid) (A(id,pl)) =
  if !bref then A(id,pl) else
  if id = oldid then (bref := true; A(newid,pl)) else
  A(id, map (rep_id bref (oldid,newid)) pl);

fun find_bound2_aux bref rref (A(id,pl)) =
  if !bref then () else
  if id = loop2_id then (bref := true; rref := SOME (List.nth (pl,2)))
  else app (find_bound2_aux bref rref) pl;

fun find_bound2 p =
  let val rref = ref NONE in find_bound2_aux (ref false) rref p;
    valOf (!rref)
  end;

fun replace_id ii p = rep_id (ref false) ii p;

fun equality_help x = pairmap (replace_id (loop2_id,loop2h_id)) x

fun induct_case_both_loop2 x =
  let
    val concl1 = pairmap (subst_one (xid,xplusone)) x
    val concl2 = equality_help concl1
    val hyp2 = equality_help x
  in
    (base_case x,(x,hyp2),(concl1,concl2))
  end;

fun induct gl = case gl of
    [] => raise ERR "induct" "empty"
  | (asw,w) :: gm =>
  let
    val _ = if [posx0] = asw then () else raise ERR "induct needs a natural" ""
    val w0 = subst_one (xid,zero) w
    val ws = subst_one (xid,xplusone) w
  in
    [([],w0),([posx0,w],ws)] @ gm
  end

fun induct2 gl = case gl of
    [] => raise ERR "induct" "empty"
  | (asw,w) :: gm =>
  let
    val _ = if [posx0] = asw then () else raise ERR "induct needs a natural" ""
    val w0 = subst_one (xid,zero) w
    val ws = subst_one (xid,xplusone) w
    val wh = eqf (replace_id (loop2_id,loop2h_id)) w
    val whs = eqf (replace_id (loop2_id,loop2h_id)) ws
  in
    [([],w0),([posx0,w,wh],ws),([posx0,w,wh],whs)] @ gm
  end

fun induct2_2 gl = case gl of
    [] => raise ERR "induct" "empty"
  | (asw,w) :: gm =>
  let
    val _ = if [posx0] = asw then () else raise ERR "induct needs a natural" ""
    val w0 = subst_one (xid,zero) w
    val w1 = subst_one (xid,one) w
    val ws = subst_one (xid,xplusone) w
    val wss = subst_one (xid,xplustwo) w
  in
    [([],w0),([],w1),([posx0,w,ws],wss)] @ gm
  end

fun induct_help x invl =
  let
    val l = x :: invl
    val concll = map (pairmap (subst_one (xid,xplusone))) l
  in
    (map base_case l,l,concll)
  end;

fun refl_eq r = if fst r = snd r then raise Proof else r;

fun eval_eq y = refl_eq (pairmap eval y)

fun hf_eq (x1,x2) = pe (hf x1 ^ " = " ^ hf x2);

fun repeat f x =
  (
  checktimer ();
  let val y = f x in
    if PolyML.pointerEq (x,y) orelse x = y then x else repeat f y
  end
  )

fun apply_concl f gl = case gl of
    [] => raise Proof
  | (asm,w) :: m => (asm, f w) :: m

fun apply_asm f gl = case gl of
    [] => raise Proof
  | (asm,w) :: m => (map f asm, w) :: m

fun pg (asm,w) =
  if null asm then pe (hf w) else
  pe (String.concatWith "\n" (map hf asm @ ["-----------------", hf w]))

fun pgl gl =
  case gl of [] => pe "Proof" | g :: l =>
  let
    val n = length gl
    val s = if n = 1 then "" else "s"
  in
    pe (its (length gl) ^ " goal" ^ s ^ " remaining");
    pg g
  end

fun refl gl = case gl of
    [] => raise Proof
  | (asm,w) :: m =>
    let val (a,b) = dest_eq w in
      if a = b then if null m then raise Proof else m
      else raise ERR "refl" "not an instance"
    end;

fun replace (p1,p2) (p3 as A(i,pl)) =
  if p3 = p1 then p2 else A (i, map (replace (p1,p2)) pl);

fun replace_asm n gl = case gl of
    [] => raise Proof
  | (asm,w) :: m =>
    let val (a,b) = dest_eq (List.nth (asm,n)) in
      (asm, replace (a,b) w) :: m
    end;

fun drop_asm gl = case gl of
    [] => raise Proof
  | (asm,w) :: m => ([hd asm],w) :: m;

fun s1 l = List.nth (l,0);
fun s2 l = List.nth (l,1);
fun s3 l = List.nth (l,2);
fun s4 l = List.nth (l,3);
fun s5 l = List.nth (l,4);
fun arg (A(i,pl)) = pl;

fun mapk k f l =
 let fun g i x = if i = k then f x else x in
   mapi g l
 end;

fun argf k f (A(i,pl)) = A(i,mapk k f pl);

fun apply_asmk k f gl = case gl of
    [] => raise Proof
  | (asm,w) :: m => (mapk k f asm, w) :: m;

fun addzero_asmk_left n gl = case gl of
    [] => raise Proof
  | (asm,w) :: m =>
    let
      val (a,b) = dest_eq (List.nth (asm,n))
      fun f x = mk_add (mk_diff (b,a),x)
    in
      (asm, lhf f w) :: m
    end;

fun apply_all f gl = case gl of
    [] => raise Proof
  | (asm,w) :: m => (map f asm, f w) :: m;

fun auto x = repeat (apply_concl (norm_poly o eqf unfold_num)) x


(* -------------------------------------------------------------------------
   Find identical loops on both side of the equation and replace them by
   a fresh variable. Idea: switch to an outside view to hide inner loops.
   ------------------------------------------------------------------------- *)

val loop_id = (0,9)
val compr_id = (0,12)
val loop2_id = (0,13)
val loop2h_id = (0,16)

fun all_outside_loop_aux r (p as A(i,pl)) =
  (
  if mem i [(0,9),(0,12),(0,13),(0,16)] then r := p :: !r else ();
  let val argl =
    if i = compr_id then tl pl else
    if i = loop_id then tl pl else
    if mem i [loop2_id, loop2h_id] then tl (tl pl) else
    pl
  in
    app (all_outside_loop_aux r) argl
  end
  )

fun all_outside_loop p = let val r = ref [] in
  all_outside_loop_aux r p; !r end;

fun list_inter l1 l2 = filter (fn x => mem x l2) l1;

fun formula_compare_size (p1,p2) =
  cpl_compare Int.compare formula_compare
  ((formula_size p1,p1), (formula_size p2,p2));

fun gen_idloop p =
  let
    val (a,b) = dest_eq p
    val l1 = all_outside_loop a
    val l2 = all_outside_loop b
    val l3 = dict_sort formula_compare_size (list_inter l1 l2)
    val v = fresh_var ()
  in
    if null l3 then p else replace (last l3,v) p
  end;

fun constant_loop2h p = case p of
    A((0,16),[a,b,c,d,e]) => if b = A((3,1),[]) then e else p
  | _ => p ;

(* -------------------------------------------------------------------------
   Goal management
   ------------------------------------------------------------------------- *)

val stack = ref []
fun execute tac =
  let val gl = (apply_all norm_poly o tac) (hd (!stack)) in
    pgl gl; stack := gl :: !stack
  end;
fun init_proof gl =
  (pgl gl; reset_var_counter (); abstimer := 0; stack := [gl]);

infixr >>;
fun op >> (f: tactic, g: tactic) x = g (apply_all norm_poly (f x));

fun is_proof tac gl = (init_proof gl; tac gl; false)
  handle Proof => true | _ => false;

fun test_pb tac pb = is_proof tac (snd pb);


(* -------------------------------------------------------------------------
   Shortcuts (at the end of the file to prevent conflicts)
   ------------------------------------------------------------------------- *)

val e = execute;
val ac = apply_concl;
val aa = apply_asm;
val aall = apply_all;
val poly = norm_poly;


end (* struct *)

(* -------------------------------------------------------------------------
   Problems from the benchmark (manual)
   ------------------------------------------------------------------------- *)

(*
load "qlang"; load "human"; load "smt_progx"; load "smt_hol";
open aiLib kernel qsyntax qrule qlang sexp;
val ERR = mk_HOL_ERR "test";
val pbl = map_snd (fn x => (abstimer := 0; aall poly x)) (get_problems ());
val _ = infix_flag := true;
val _ = x_flag := true;
val _ = abstimer := 0;

val (anum,gl) = List.nth (pbl,0); init_proof gl;
val proof1 = ac decouple >> induct2 >> auto >> refl >>
 (ac unfold) >> (replace_asm 2 o replace_asm 1) >> refl >>
 (ac unfold) >> (replace_asm 2 o replace_asm 1) >> refl;
val (pbl1,pbl2) = partition (test_pb proof1) pbl; length pbl1; (* 62 *)

val (anum,gl) = List.nth (pbl2,4); init_proof gl;
val proof2 = ac decouple >> induct >> auto >> refl >>
 ac unfold >> replace_asm 1 >> ac (replace_atl constant_loop2h) >>
 refl;
val (pbl5,pbl6) = partition (test_pb proof2) pbl2; length pbl5; (* 43 *)

val (anum,gl) = List.nth (pbl6,0); init_proof gl;
val proof4 = induct >> auto >> refl >>
  ac unfold >> replace_asm 1 >> ac gen_idloop >> drop_asm >> induct >>
  repeat (ac unfold) >> refl >>
  ac unfold >> replace_asm 1 >> refl;
val (pbl7,pbl8) = partition (test_pb proof4) pbl6; length pbl7; (* 2 *)

val (anum,gl) = List.nth (pbl8,0); init_proof gl;
val proof5 = induct2_2 >> auto >> refl >> auto >> refl >>
  ac unfold >> ac (lhf unfold) >> apply_asmk 2 (lhf unfold) >>
  addzero_asmk_left 2 >> replace_asm 1 >> ac (rhf (argf 1 unfold)) >> refl;
val (pbl9,pbl10) = partition (test_pb proof5) pbl8; length pbl9; (* 17 *)

val (anum,gl) = List.nth (pbl10,0); init_proof gl;
val proof6 = auto >> refl;
val (pbl11,pbl12) = partition (test_pb proof6) pbl10; length pbl11; (* 618 *)

val (anum,gl) = List.nth (pbl12,0); init_proof gl;
val proof7 = induct >> auto >> refl >> 
  ac unfold >> replace_asm 1 >> ac gen_idloop >> drop_asm >> induct
  auto >> refl


fun simplify 






v(x) = 2^(n+1)
u(x) = 2^x * u(x-1) + u(x-1)

1 3 15 135

u(x) = 2^x * u(x-1) + u(x-1)
1 2^n*1

x 1




u(x+1) = v(x) + 2
v(x+1) = u(x)+ v(x)

u(x+2) = u(x) + v(x) + 2
       = u(x) + u(x+1)

1 2
4 3
5 7
9 12
14 21

u(x+2) = u(x+1) + u(x)
1 3
4 1
5 4
9 5
14





e induct2;




*)
