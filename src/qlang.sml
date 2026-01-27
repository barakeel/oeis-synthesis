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
  if id = add_id orelse id = mult_id orelse id = diff_id
  then A(id, map norm_poly_done argl)
  else A(id, map norm_poly argl)

fun addzero_asmk_left n gl = case gl of
    [] => raise Proof
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
    case list_compare formula_compare (m1,m2) of
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
      if is_greater0 pb' then
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
   Loop definitions
   ------------------------------------------------------------------------- *)

val defd = ref (dempty Int.compare)
val idefd = ref (dempty formula_compare)
val def_counter = ref 0

fun add_key key argl =
  case dfindo key (!idefd) of 
    SOME oldn => A ((6,oldn),argl) 
  | NONE => 
    let 
      val value = !def_counter
      val _ = incr def_counter
    in
      idefd :=  dadd key value (!idefd); 
      defd := dadd value key (!defd); 
      A ((6,value),argl)  
    end 

fun def_one p =  case p of
    A ((0,9),[pa,pb,pc]) => add_key (A ((0,9),[pa])) [pb,pc]
  | A (id,[pa,pb,pc,pd,pe]) =>
    if not (mem id [(0,13),(0,16)]) then raise ERR "def_one" "" else
    add_key (A (id,[pa,pb])) [pc,pd,pe]
  | _ => raise ERR "def_one" ""
  
fun undef_one p = case p of
    A ((6,n),argl) => 
    (
    case dfindo n (!defd) of NONE => p | SOME (A (id,hoargl)) => 
      if not (mem id [(0,9),(0,13),(0,16)]) then p
      else A (id, hoargl @ argl)
    )
    | _ => p

(* -------------------------------------------------------------------------
   Parsing the conjecture
   ------------------------------------------------------------------------- *)

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
   Induction
   ------------------------------------------------------------------------- *)

val xid = (3,0);
val xplusone = mk_add (mk_var 0, one);
val xplustwo = mk_add (mk_var 0, A ((1,2),[]));

fun rep_id bref (oldid,newid) (A(id,pl)) =
  if !bref then A(id,pl) else
  if id = oldid then (bref := true; A(newid,pl)) else
  A(id, map (rep_id bref (oldid,newid)) pl);

fun replace_id ii p = rep_id (ref false) ii p;

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
    [] => raise Proof
  | (asm,w) :: m => (asm, f w) :: m

fun apply_asm f gl = case gl of
    [] => raise Proof
  | (asm,w) :: m => (map f asm, w) :: m

fun apply_all f gl = case gl of
    [] => raise Proof
  | (asm,w) :: m => (map f asm, f w) :: m;

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

fun imitate (gl:goal list) = 
  (
  checktimer ();
  case gl of [] => raise Proof | ((asm,w) :: m) => 
  (
  if not (is_eq w) then gl else
  case dest_eq w of
    (A((0,9),[pa,pb,pc]),A((0,9),[pa',pb',pc'])) => 
    (rev [(asm, mk_eq (pa,pa')), (asm, mk_eq (pb,pb')), (asm, mk_eq (pc,pc'))]) 
    @ m
  | (A((0,13),[pa,pb,pc,pd,pe]),A((0,13),[pa',pb',pc',pd',pe'])) => 
    (rev [(asm, mk_eq (pa,pa')), (asm, mk_eq (pb,pb')), (asm, mk_eq (pc,pc')),
     (asm, mk_eq (pd,pd')), (asm, mk_eq (pe,pe'))]) @ m
  | _ => gl
  )
  );


(* -------------------------------------------------------------------------
   Goal management
   ------------------------------------------------------------------------- *)

val stack = ref []
fun execute tac =
  let val gl = (apply_all norm_poly o tac) (hd (!stack)) in
    pgl gl; stack := gl :: !stack
  end;
fun init_proof gl =
  (reset_var_counter (); def_counter := 0; abstimer := 0; stack := [gl]);

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

