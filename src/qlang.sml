(* ========================================================================= *)
(* Language for the Qprover                                                  *)
(* ========================================================================= *)

structure qlang :> qlang = struct

open HolKernel Abbrev boolLib aiLib kernel qsyntax qrule sexp
val ERR = mk_HOL_ERR "qlang"

type formula = qsyntax.formula
type qprove = (formula list * (prog * int))
type goal = formula list * formula
type tactic = goal list -> goal list
type proof = string list
type proofe = proof * (int * int)
type entry = goal list * proofe list


fun goal_size (asm,w) = sum_int (map formula_size (w :: asm));
fun goall_size gl = sum_int (map goal_size gl);
fun goal_compare ((asm1,w1),(asm2,w2)) = 
  list_compare formula_compare (w1 :: asm1, w2 :: asm2)
val goall_compare = list_compare goal_compare

fun goal_to_sexp (asm,w) = Sexp (map formula_to_sexp (w :: asm))
fun sexp_to_goal x = case x of 
   Sexp (w :: asm) => (map sexp_to_formula asm, sexp_to_formula w)
 | _ => raise ERR "sexp_to_goal" ""
 
fun goall_to_sexp gl = Sexp (map goal_to_sexp gl)
fun sexp_to_goall x = case x of 
    Sexp gl => map sexp_to_goal gl 
  | _ => raise ERR "sexp_to_goall" ""
 
(* -------------------------------------------------------------------------
   Misc
   ------------------------------------------------------------------------- *)

val xid = (3,0)
val yid = (3,1)

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

fun depends_on id (p as A (i,pl)) = 
  (
  checktimer ();
  if i = id then true else 
  let val pl' = 
    if mem i [compr_id,loop_id] then tl pl
    else if mem i [loop2_id, loop2h_id] then snd (part_n 2 pl)
    else pl
  in
    exists (depends_on id) pl'
  end
  );

fun cumul_distrib_aux (tot:real) l = case l of
    [] => []
  | (mv,p) :: m => (mv, tot + p) :: cumul_distrib_aux (tot + p) m

fun cumul_distrib l = cumul_distrib_aux 0.0 l;

fun sample_cumul (alea :real) cumul = case cumul of
    []  => raise ERR "find_cumul" ""
  | [(key,p)] => (key,p)
  | (key,p) :: m => if alea < p then (key,p) else sample_cumul alea m;

fun sample_distrib l = 
  sample_cumul (random_real ()) (cumul_distrib (normalize_distrib l));

(* -------------------------------------------------------------------------
   Syntactic analysis
   ------------------------------------------------------------------------- *)

fun find_loop2h p = case p of
    A ((0,16),_) => SOME p 
  | A (_, pl) => find_loop2hl pl
and find_loop2hl pl = case pl of
    [] => NONE
  | p :: pm => 
    (case find_loop2h p of SOME r => SOME r | NONE => find_loop2hl pm) 
;
fun find_loop (p as A (id,pl)) = if is_loopid id then SOME p else find_loopl pl
and find_loopl pl = case pl of
    [] => NONE
  | p :: pm => (case find_loop p of SOME r => SOME r | NONE => find_loopl pm);

(* -------------------------------------------------------------------------
   Arithmetical reasoning
   ------------------------------------------------------------------------- *)

fun add_poly (p1,p2) =
  (
  checktimer ();
  case (p1,p2) of
    ([], p) => p
  | (p, []) => p
  | ((m1,c1) :: ms1, (m2,c2):: ms2) =>
    (
    case list_compare formula_compare_timed (m1,m2) of
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
    case formula_compare_timed (a1,a2) of
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

fun mono_to_formula (xl,coeff) =
  if coeff = 1
  then (if null xl then one else mono_to_formula1 xl)
  else (if null xl then mk_int coeff else 
        mk_mult (mk_int coeff, mono_to_formula1 xl))
   
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
  if id = add_id orelse id = mult_id orelse id = diff_id
  then A(id, map norm_poly_done argl)
  else A(id, map norm_poly argl)

fun addzero_asmk_left n gl = case gl of
    [] => []
  | (asm,w) :: m =>
    let
      val (a,b) = dest_eq (List.nth (asm,n))
      fun f x = mk_add (mk_diff (b,a),x)
    in
      (asm, lhf f w) :: m
    end;


fun simp_poly (p1,p2) =
  (
  checktimer ();
  case (p1,p2) of
    ([],_) => (p1,p2)
  | (_,[]) => (p1,p2)
  | ((m1,c1) :: ms1, (m2,c2):: ms2) =>
    (
    case list_compare formula_compare_timed (m1,m2) of
      EQUAL =>
      let val c = c1 - c2 in
        if c = 0 then simp_poly (ms1, ms2) else 
         let val (newp1,newp2) = simp_poly (ms1, ms2) in
           ((m1,c) :: newp1, newp2)
         end
      end
    | LESS => 
      let val (newp1,newp2) = simp_poly (ms1, p2) in
        ((m1,c1) :: newp1, newp2)
      end
    | GREATER =>
      let val (newp1,newp2) = simp_poly (p1, ms2) in
        (newp1, (m2, c2) :: newp2)
      end
    )
  )  

fun simp formula = 
  if not (is_eq formula) then formula else 
  let 
    val (a,b) = dest_eq formula; 
    val (c,d) = simp_poly (formula_to_poly a,formula_to_poly b)
  in
    mk_eq (poly_to_formula c, poly_to_formula d)
  end;

(* -------------------------------------------------------------------------
   Testing if an expression is greater or equal to 0.
   ------------------------------------------------------------------------- *)

fun is_geq0 l = 
  (
  checktimer ();
  case l of
    [] => true
  | A ((1,i),[]) :: m => if i >= 0 then is_geq0 m else false
  | A (id,pl) :: m =>
    if id = xid then is_geq0 m else
    if mem id [add_id, mult_id, div_id, mod_id] then is_geq0 (pl @ m)
    else false
  )
  
fun is_greater0 p = is_geq0 [norm_poly (mk_diff (p,one))]

fun is_leq0 p = is_geq0 [norm_poly (mk_diff (zero,p))]

(* -------------------------------------------------------------------------
   Unfolding loops
   ------------------------------------------------------------------------- *)

fun replace_atl f (p as A(id,pl)) = 
  (
  checktimer ();
  if is_loopid id then f p else A (id, map (replace_atl f) pl)
  )
  

fun replace_atlh f (p as A(id,pl)) = 
  (
  checktimer (); 
  if id = loop2h_id then f p else A (id, map (replace_atlh f) pl) 
  )
  
fun replace_bu f (p as A(id,pl)) = 
  (
  checktimer ();
  let val newpl = map (replace_bu f) pl in
    if is_loopid id then f (A(id,newpl)) else A(id,newpl)
  end
  )

fun unfold_one p = 
  (
  checktimer ();
  case p of
    A ((0,9),[pa,pb,pc]) =>
    if is_greater0 pb then
      let
        val xrep = A ((0,9),[pa, mk_diff (pb,one), pc])
        val yrep = pb
      in
        substl [(xid,xrep),(yid,yrep)] pa
      end
    else if is_leq0 pb then pc
    else p
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
    else p
  | _ => p
  )

fun unfold p = replace_atl unfold_one p;
fun unfoldh p = replace_atlh unfold_one p;

fun unfold_num_one p = 
  (
  checktimer ();
  case p of
    A ((0,9),[pa,pb,pc]) =>
    let val pb' = eval pb in
      if not (is_num pb') then p else
      if is_greater0 pb' then
        let
          val xrep = A ((0,9),[pa, mk_diff (pb',one), pc])
          val yrep = pb
        in
          substl [(xid,xrep),(yid,yrep)] pa
        end
      else if is_leq0 pb then pc
      else p
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
      else p
    end
  | _ => p
  )
  
fun unfold_num p = replace_bu unfold_num_one p;

(* -------------------------------------------------------------------------
   Induction
   ------------------------------------------------------------------------- *)

val two = A ((1,2),[])
val xplusone = mk_add (mk_var 0, one)
val xplustwo = mk_add (mk_var 0, two)

fun rep_id bref (oldid,newid) (A(id,pl)) =
  if !bref then A(id,pl) else
  if id = oldid then (bref := true; A(newid,pl)) else
  A(id, map (rep_id bref (oldid,newid)) pl);

fun replace_id ii p = rep_id (ref false) ii p;

fun induct_cond asm = if null asm then () else raise ERR "induct" "hypothesis"

fun induct gl = 
  (
  checktimer ();
  case gl of
    [] => raise ERR "induct" "empty"
  | (asm,w) :: gm =>
  let
    val _ = induct_cond asm
    val w0 = subst_one (xid,zero) w
    val ws = subst_one (xid,xplusone) w
  in
    [([],w0),([w],ws)] @ gm
  end
  )
  
fun induct2 gl = 
  (
  checktimer ();
  case gl of 
    [] => raise ERR "induct" "empty"
  | (asm,w) :: gm =>
  let
    val _ = induct_cond asm
    val w0 = subst_one (xid,zero) w
    val w1 = subst_one (xid,one) w
    val ws = subst_one (xid,xplusone) w
    val wss = subst_one (xid,xplustwo) w
  in
    [([],w0),([],w1),([w,ws],wss)] @ gm
  end
  )

fun induct_para gl = 
  (
  checktimer ();
  case gl of
    [] => raise ERR "induct" "empty"
  | (asm,w) :: gm =>
  let
    val _ = induct_cond asm
    val w0 = subst_one (xid,zero) w
    val ws = subst_one (xid,xplusone) w
    val wh = eqf (replace_id (loop2_id,loop2h_id)) w
    val whs = eqf (replace_id (loop2_id,loop2h_id)) ws
  in
    [([],w0),([w,wh],ws),([w,wh],whs)] @ gm
  end
  )
  
(* -------------------------------------------------------------------------
   Wrappers
   ------------------------------------------------------------------------- *)

fun repeat f x =
  (
  checktimer ();
  let val y = f x in
    if PolyML.pointerEq (x,y) orelse x = y then x else repeat f y
  end
  )

fun apply_concl f gl = case gl of
    [] => []
  | (asm,w) :: m => (asm, f w) :: m

fun apply_asm f gl = case gl of
    [] => []
  | (asm,w) :: m => (map f asm, w) :: m

fun apply_all f gl = case gl of
    [] => []
  | (asm,w) :: m => (map f asm, f w) :: m;

fun pg (asm,w) =
  if null asm then pe (hf w) else
  pe (String.concatWith "\n" (map hf asm @ ["-----------------", hf w]))

fun pgl gl =
  case gl of [] => pe "Proof." | g :: l =>
  let
    val n = length gl
    val s = if n = 1 then "" else "s"
  in
    pe (its (length gl) ^ " goal" ^ s ^ " remaining");
    pg g
  end

fun refl gl = case gl of [] => [] | (asm,w) :: m =>
  if not (is_eq w) orelse not ((op =) (dest_eq w)) then gl else m


fun replace (p1,p2) (p3 as A(i,pl)) =
  if p3 = p1 then p2 else A (i, map (replace (p1,p2)) pl);

fun replace_asm n gl = 
  (
  checktimer ();
  case gl of
    [] => []
  | (asm,w) :: m =>
    let val (a,b) = dest_eq (List.nth (asm,n)) in
      (asm, replace (a,b) w) :: m
    end
  )
fun replace_asm_sym n gl = case gl of
    [] => []
  | (asm,w) :: m =>
    let val (a,b) = dest_eq (List.nth (asm,n)) in
      (asm, replace (b,a) w) :: m
    end;

fun drop_asm gl = case gl of
    [] => []
  | (asm,w) :: m => ([],w) :: m;

fun tl_asm gl = case gl of [] => []
  | (asm,w) :: m => (tl asm,w) :: m;

fun argf k f (A(i,pl)) = A(i,mapk k f pl);

fun apply_asmk k f gl = case gl of
    [] => []
  | (asm,w) :: m => (mapk k f asm, w) :: m;

fun auto x = repeat (apply_concl (norm_poly o eqf unfold_num)) x

(* -------------------------------------------------------------------------
   Generalizations
   ------------------------------------------------------------------------- *)

val loop_id = (0,9)
val compr_id = (0,12)
val loop2_id = (0,13)
val loop2h_id = (0,16)

fun all_outside_loop_aux r (p as A(i,pl)) =
  (
  if mem i [loop_id, compr_id, loop2_id, loop2h_id] then r := p :: !r else ();
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

fun formula_compare_size_timed (p1,p2) =
  cpl_compare Int.compare formula_compare_timed
  ((formula_size p1,p1), (formula_size p2,p2));

fun gen_idloop_aux p =
  let
    val (a,b) = dest_eq p
    val l1 = all_outside_loop a
    val l2 = all_outside_loop b
    val l3 = dict_sort formula_compare_size_timed (list_inter l1 l2)
    val v = fresh_var ()
  in
    if null l3 then p else replace (last l3,v) p
  end;

fun decouple_one v p =  case p of
    A ((0,9),[pa,pb,pc]) =>
    let val pc' = subst_one (xid,v) pc in
      A ((0,9),[pa,pb,pc'])
    end
  | A (id,[pa,pb,pc,pd,pe]) =>
    if not (mem id [(0,13),(0,16)])
      then raise ERR "decouple_loop" "not a loop"
    else
    let
      val pd' = subst_one (xid,v) pd
      val pe' = subst_one (xid,v) pe
    in
      A (id,[pa,pb,pc,pd',pe'])
    end
  | _ => raise ERR "decouple_loop" "not a loop"

fun decouple1_aux p =
  (
  checktimer ();
  let val v = fresh_var () in replace_atl (decouple_one v) p end
  )
  
fun subst_nobound (v,p) (A (i,pl)) = 
  (
  checktimer ();
  if i = v then p 
  else if mem i [compr_id,loop_id] then 
    let val (al,bl) = part_n 2 pl in 
      A (i, al @  map (subst_nobound (v,p)) bl) 
    end
  else if mem i [loop2_id, loop2h_id] then 
    let val (al,bl) = part_n 3 pl in 
      A (i, al @  map (subst_nobound (v,p)) bl) 
    end
  else A (i, map (subst_nobound (v,p)) pl)
  )

fun decouple2_aux p = 
   let val v = fresh_var () in subst_nobound ((3,0),v) p end

fun swap_var_aux n = substl [((3,0),mk_var 1),((3,n),mk_var 0)];

val decouple1 = apply_concl decouple1_aux
val decouple2 = apply_concl decouple2_aux
val gen_idloop = apply_concl gen_idloop_aux
fun swap_var n = apply_concl (swap_var_aux n)

(* -------------------------------------------------------------------------
   Prove that the arguments are equal if top symbol is the same
   ------------------------------------------------------------------------- *)

fun imitate (gl:goal list) = 
  (
  checktimer ();
  case gl of [] => [] | ((asm,w) :: m) => 
    if not (is_eq w) then gl else
    let val (A(id1,argl1), A(id2,argl2)) = dest_eq w in
      if id1 <> id2 then gl else
      rev (map (fn x => (asm,mk_eq x)) (combine (argl1,argl2))) @ m
    end
  );

(* -------------------------------------------------------------------------
   Custom functions usually to eliminate loop2h
   ------------------------------------------------------------------------- *)

fun strip_mult p = case p of
    A ((0,5),pl) => List.concat (map strip_mult pl)
  | _ => [p]

fun count x l = length (filter (fn y => y = x) l)

fun is_linear p = count (mk_var 0) (strip_mult p) = 1

fun pow_mult p = case p of 
  A ((0,9), [pa, pb, pc]) => 
  if not (is_linear pa) then p else mk_mult (A ((0,9), [pa, pb, one]), pc)
  | _ => p;

fun constant_loop2h p = 
  case p of
    A((0,16),[a,b,c,d,e]) => if b = A((3,1),[]) then e else p
  | _ => p

fun linear_loop2h p = case p of
    A((0,16),[a,b,c,d,e]) => 
    (
    case b of A((0,3),[coeff,A((3,1),[])]) =>
      if is_num coeff then mk_add (mk_mult (coeff,c), e) else p
    | _ => p
    )
  | _ => p ;

fun add_eq_sym eq formula = 
  let val (a,b) = dest_eq eq in
    mk_add (formula, mk_diff (b,a))
  end;

(* eliminates loop2h by replacing it by the loop2 above it *)
fun fold_one n top = case find_loop2h top of 
    SOME (A ((0,16),[pa,pb,pc,pd,pe])) => 
    let 
      val r = A ((0,13),[pa,pb,mk_add (pc,one),pd,pe])
      val eq1 = mk_eq (r,r) 
      val eq2 = lhf unfold eq1
    in
      funpow n (add_eq_sym eq2) top
    end
  | _ => top;

(* eliminates loop2h by replacing it by loop *)
fun loop2h_to_loop p = case p of
  A((0,16),[a,b,c,d,e]) => 
    if depends_on (3,0) b then p else 
      A (loop_id, [subst_one ((3,1), mk_var 0) b,c,e])
  | _ => p
  ;

val foldlh = apply_concl (lhf (fold_one 1));
val foldrh = apply_concl (rhf (fold_one 1));

(* -------------------------------------------------------------------------
   Conjecturing
   ------------------------------------------------------------------------- *)

fun conjecture tmo gl = case (gl,tmo) of ([],_) => [] | (gl,NONE) => gl |
  ((asm,w) :: m, SOME tm) => ([],tm) :: (tm :: asm, w) :: m;
   
fun cj2_aux gl = case gl of [] => NONE | (asm,w) :: m =>
  if not (is_eq w) then NONE else
  let val (a,b) = dest_eq w in
    SOME (mk_eq (valOf (find_loop a), valOf (find_loop b)))
  end;

fun cj2 gl = conjecture (cj2_aux gl) gl;   

fun cj3_aux gl = case gl of [] => NONE | (asm,w) :: m => 
  if not (is_eq w) then NONE else
  let val tm = valOf (find_loop (List.nth (asm,1))) in 
    SOME (mk_eq (tm,tm))
  end;

fun cj3 gl = conjecture (cj3_aux gl) gl;   

(* -------------------------------------------------------------------------
   Goal management
   ------------------------------------------------------------------------- *)

val stack = ref []
val tactic_counter = ref 0

fun apply_tac tac gl =
  let 
    val _ = abstimer := 0
    val _ = incr tactic_counter
    val gl1 = tac gl handle Interrupt => raise Interrupt | _ => gl
    val gl2 = apply_all norm_poly gl1 
      handle Interrupt => raise Interrupt | _ => gl1
  in
    refl gl2
  end

fun execute tac =
  let val gl = apply_tac tac (hd (!stack)) in
    if null (!stack) then pe "Proof." 
    else if hd (!stack) = gl then pe "This tactic had no effect."
    else (pgl gl; stack := gl :: !stack)
  end;

fun back () = case !stack of 
    _ :: a :: m => (stack := a :: m; pgl a) 
  | _ => raise ERR "back" ""

fun init_proof gl =
  (reset_var_counter (); abstimer := 0; stack := [gl]);

infix >>;
fun op >> (gl,tac) = apply_tac tac gl

fun is_proof tac gl = null (init_proof gl; tac gl)
fun test_pb tac pb = is_proof tac (snd pb);

fun init_pb pbl = 
  let val (anum,gl) = List.nth (pbl,0) in init_proof gl; pgl gl end;

(* -------------------------------------------------------------------------
   Storage
   ------------------------------------------------------------------------- *)


fun entry_to_string (gl,(stacl,(size,time))) = 
  sexp_to_string (Sexp (goall_to_sexp gl :: Atom (its size) :: Atom (its time) :: map Atom stacl))
  
fun to_disk file data = writel (selfdir ^ "/" ^ file) 
  (map entry_to_string (distrib data))

fun dest_atom sexp = case sexp of Atom s => s | _ => raise ERR "dest_atom" ""  
fun string_to_entry s = case string_to_sexp s of 
    Sexp (a :: b :: c :: m) => (sexp_to_goall a, 
     [(map dest_atom m, 
       (string_to_int (dest_atom b), string_to_int (dest_atom c)))])
  | _ => raise ERR "string_to_entry" ""
  
fun from_disk file = map string_to_entry (readl (selfdir ^ "/" ^ file))


val compare_proof = list_compare String.compare

fun less_time (s1,(n1,t1)) (s2,(n2,t2)) = 
  triple_compare Int.compare Int.compare compare_proof ((t1,n1,s1),(t2,n2,s2)) 
  = LESS
   
fun less_size (s1,(n1,t1)) (s2,(n2,t2)) = 
  triple_compare Int.compare Int.compare compare_proof ((n1,t1,s1),(n2,t2,s2)) 
  = LESS

fun find_min_loop lessf a m = case m of
    [] => a
  | a' :: m' => find_min_loop lessf (if lessf a' a then a' else a)  m'

fun find_min lessf l = case l of 
    [] => raise ERR "find_min" ""
  | a :: m => find_min_loop lessf a m

val proofd = ref (dempty goall_compare)

fun init_proofd () = proofd := dempty goall_compare
 
fun update_proofd (gl,value) = 
  let 
    val oldvalue = case dfindo gl (!proofd) of NONE => [] | SOME l => l 
    val tempvalue = value @ oldvalue  
    val minsize = find_min less_size tempvalue
    val mintime = find_min less_time tempvalue
    val newvalue =  mk_sameorder_set (fst_compare compare_proof) 
      [minsize,mintime]
  in
    proofd := dadd gl newvalue (!proofd)
  end
  
fun update_proofd_one (gl,(proof,t)) = 
  update_proofd (gl,[(proof,(length proof,t))])  
 
fun get_proofd () = dlist (!proofd)


(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val search_depth = 40
val gl_maxsize = 200

fun uniform_policy tacl (_ : goal list) = map (fn x => (x,1.0)) tacl;

fun search_aux gltop acc t nmax n policy gl = 
  if null gl then update_proofd_one (gltop,(rev acc,t)) else 
  if n >= nmax orelse goall_size gl > gl_maxsize then () else 
  let 
    val (stac: string, tac) = fst (sample_distrib (policy gl)) 
    val newgl = apply_tac tac gl 
    val newt = t + (!abstimer)
    val _ = dbgf (fn () => (pe stac; pgl newgl))
    val newacc = stac :: acc
  in
    if newgl = gl 
    then search_aux gltop acc t nmax (n+1) policy gl 
    else search_aux gltop newacc newt nmax (n+1) policy newgl
  end
  
fun search nmax policy gl = search_aux gl [] 0 nmax 0 policy gl
  
fun retry t policy gltop = 
  let 
    val limit = Time.fromReal t   
    val rt = Timer.startRealTimer ()
    fun try gl = 
      (
      reset_var_counter ();
      if Timer.checkRealTimer rt > limit then () else 
      (search search_depth policy gl; try gl)
      )  
  in 
    try gltop
  end;

(* -------------------------------------------------------------------------
   Record (also remove ineffective tactics)
   ------------------------------------------------------------------------- *) 
  
fun record_aux gltop acc t stacl gl = case (gl,stacl) of
    ([],_) => update_proofd_one (gltop,(rev acc,t))
  | (_,[]) => ()
  | (_, (stac : string ,tac) :: m) => 
    let val newgl = apply_tac tac gl in
      dbgf (fn () => (pe stac; pgl gl));
      if newgl = gl then record_aux gltop acc t m gl else
      record_aux gltop (stac :: acc) (t + (!abstimer)) m newgl
    end;

fun record proof gl = 
  (
  dbgf (fn () => pgl gl);
  record_aux gl [] 0 proof gl
  );
  
(* -------------------------------------------------------------------------
   Problems
   ------------------------------------------------------------------------- *)

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
      (a, [([], mk_eq (prog_to_formula p1, prog_to_formula p2))])
    val l4 = map f appl3
    val l5 = map_snd (fn x => (abstimer := 0; apply_all norm_poly x)) l4
    val l6 = dict_sort compare_imin (map_assoc (goall_size o snd) l5)
  in
    map fst l6  
  end

fun changed a b = (if length a = b then () else 
  raise ERR "changed" (its b ^ " -> " ^ its (length a)));

(* -------------------------------------------------------------------------
   Shortcuts
   ------------------------------------------------------------------------- *)
   
val e = execute;
val ac = apply_concl;
val aa = apply_asm;
val aall = apply_all;

end (* struct *)

