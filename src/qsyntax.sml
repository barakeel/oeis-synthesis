(* ========================================================================= *)
(* DESCRIPTION   : Syntax of Qprover                                         *)
(* ========================================================================= *)

structure qsyntax :> qsyntax = struct

open HolKernel Abbrev boolLib aiLib kernel sexp
val ERR = mk_HOL_ERR "qsyntax"

(* -------------------------------------------------------------------------
   Timers
   ------------------------------------------------------------------------- *)

fun checktimern n = 
  (
  abstimer := !abstimer + n; 
  if !abstimer > !timelimit then raise ProgTimeout else ()
  )

fun checktimer () = checktimern 1

(* -------------------------------------------------------------------------
   Instructions:
   0 1 2 3 4 5 6 7 8    9  10 11 12    13    14   15
   A B C D E F G H I    J    K L M     N     O    P
   0 1 2 + - * / % cond loop x y compr loop2 push pop
   ------------------------------------------------------------------------- *)

type id = int * int

datatype formula = A of (id * formula list) 

val add_id = (0,3)
val diff_id = (0,4)
val mult_id = (0,5)
val div_id = (0,6)
val mod_id = (0,7)
val cond_id = (0,8)
val loop_id = (0,9)
val compr_id = (0,12)
val loop2_id = (0,13)
val loop2h_id = (0,16)

val not_id = (5,0)
val or_id = (5,1)
val forall_id = (5,2)
val eq_id = (5,3)
val geq_id = (5,4)

val convertv = Vector.fromList
  [(1,0),(1,1),(1,2),
   add_id,diff_id,mult_id,div_id,mod_id,cond_id,loop_id,
   (3,0),(3,1),
   compr_id, loop2_id]
   
fun prog_to_formula (Ins (id,pl)) = 
  A (Vector.sub (convertv,id), map prog_to_formula pl)

(* -------------------------------------------------------------------------
   Syntax (constant 0, integer 1, skolem 2, variable 3, bound variable)
   ------------------------------------------------------------------------- *) 

fun cid i = (0,i)
fun iid i = (1,i)
fun sid i = (2,i)
fun vid i = (3,i)
fun bid i = (4,i)

fun is_progid i = fst i = 0
fun is_numid i = fst i = 1
fun is_skolemid i = fst i = 2
fun is_varid i = fst i = 3
fun is_logicid i = fst i = 5

val var_counter = ref 0
fun fresh_var () = (incr var_counter; A((3,!var_counter),[]))
fun reset_var_counter () = var_counter := 0

val skolem_counter = ref 0
fun fresh_skolemid () = 
  let val skid = sid (!skolem_counter) in
    incr skolem_counter; skid
  end
fun reset_skolem_counter () = skolem_counter := 0

fun id_compare (a,b) = cpl_compare Int.compare Int.compare (a,b)

fun is_num (A (id,_)) = is_numid id
fun is_eq (A (id,_)) = id = eq_id
fun is_neg (A (id,_)) = id = not_id
fun is_boolean (A ((ty,id),_)) = id >= 0 andalso id <= 3
fun neg f = case f of A ((0,0),[g]) => g | _ => A (not_id,[f])

fun formula_compare (A x,A y) =
  (
  checktimer ();
  cpl_compare id_compare (list_compare formula_compare) (x,y)
  )
  
fun formula_size (A (id,l)) = 1 + sum_int (map formula_size l)

fun formula_compare_size (p1,p2) = 
  cpl_compare Int.compare formula_compare 
  ((formula_size p1,p1), (formula_size p2,p2))
  
val zero = A (iid 0,[])
val one = A (iid 1,[])
fun mk_eq (f1,f2) = A (eq_id,[f1,f2])
fun mk_geq (f1,f2) = A (geq_id,[f1,f2])
fun mk_add (f1,f2) = A (add_id,[f1,f2])
fun mk_mult (f1,f2) = A (add_id,[f1,f2])
fun mk_diff (f1,f2) = A (diff_id,[f1,f2])
fun mk_var i = A (vid i,[])
fun mk_int i = A (iid i,[])

fun dest_eq (A(id,l)) = 
  if id = eq_id then pair_of_list l else raise ERR "dest_eq" ""

fun eqf f x = let val (a,b) = dest_eq x in mk_eq (f a, f b) end 
fun lhf f x = let val (a,b) = dest_eq x in mk_eq (f a, b) end 
fun rhf f x = let val (a,b) = dest_eq x in mk_eq (a, f b) end 

(* -------------------------------------------------------------------------
   Tagged formulas and evaluation
   ------------------------------------------------------------------------- *)

datatype formulat = At of (id * bool * formulat list) 

fun true_tag (At(_,b,_)) = b

fun tag_ground (A (i,pl)) =
  let 
    val pl' = map tag_ground pl 
    val pl'' = 
      if i = compr_id orelse i = loop_id then tl pl' else
      if i = loop2_id then tl (tl pl') else pl'
    val b = not (is_varid i) andalso all true_tag pl'' 
  in
    At (i,b,pl') 
  end

fun untag (At(i,b,pl)) = A(i,map untag pl)

fun is_ground (A (i,pl)) =
  (
  checktimer ();
  not (is_varid i) andalso
  if i = compr_id then all is_ground (tl pl) else
  if i = loop_id then all is_ground (tl pl) else 
  if i = loop2_id then all is_ground (tl (tl pl)) else 
  all is_ground pl
  )

fun mk_exec_at (At (id,_,pl)) = 
  let val fl = map mk_exec_at pl in 
    if is_progid id then Vector.sub (exec.execv,snd id) fl else
    if is_numid id then (fn _ => (checktimer (); IntInf.fromInt (snd id))) else
    if is_varid id andalso mem (snd id) [0,1] 
      then Vector.sub (exec.execv, snd id + 10) fl
    else raise ERR "mk_exec_at" ""
  end

fun eval_aux (At (i,b,pl)) =
  if not b orelse null pl then (At (i, b, map eval_aux pl)) else
  let 
    val exec = mk_exec_at (At (i,b,pl)) 
    val r = exec (IntInf.fromInt 0, IntInf.fromInt 0, IntInf.fromInt 0)
  in
    At ((1,IntInf.toInt r),true,[])
  end

(* replace all ground terms by integer value *)
fun eval p = untag (eval_aux (tag_ground p))


(* -------------------------------------------------------------------------
   Human interface
   ------------------------------------------------------------------------- *) 

val prognamel = ["0u","1u","2u",
  "+","-","*","div","mod","cond","loop","xu","yu","compr","loop2","pus","pop",
  "loop2h"]
val prognamev = Vector.fromList prognamel
val prognamed = dnew String.compare (number_snd 0 prognamel);

val logicnamel = ["not","or","forall","=",">="]
val logicnamev = Vector.fromList logicnamel
val logicnamed = dnew String.compare (number_snd 0 logicnamel);

fun id_of_oper s = 
  if hd_string s = #"x" 
    then (3, string_to_int (tl_string s))
  else if String.isPrefix "sk" s 
    then (2, string_to_int (tl_string (tl_string s)))
  else if can string_to_int s
    then (1, string_to_int s)
  else (
       (0, dfind s prognamed) handle NotFound =>
         ((5, dfind s logicnamed) handle NotFound => raise ERR "id_of_oper" s)
       )
  
fun sexp_to_formula phi = case phi of
    Atom s => A (id_of_oper s,[])
  | Sexp (Atom s :: argl) => A (id_of_oper s, map sexp_to_formula argl)
  | _ => raise ERR "sexp_to_formula" "";

val infix_flag = ref false

fun human_of_id (i1,i2) = 
  if i1 = 5 then
    if i2 >= Vector.length logicnamev orelse i2 < 0
    then raise ERR "human_of_formula" ("undefined logic: " ^ its i2) 
    else Vector.sub (logicnamev,i2)
  else
  if i1 = 6 then "u" ^ its i2 else
  if i1 = 3 then "x" ^ its i2 else
  if i1 = 2 then "sk" ^ its i2 else
  if i1 = 1 then its i2 else
  if i1 = 0 then
    if i2 >= Vector.length prognamev orelse i2 < 0
    then raise ERR "human_of_formula" ("undefined prog: " ^ its i2) 
    else Vector.sub (prognamev,i2)
  else raise ERR "human_of_formula" ("undefined class: " ^ its i1) 

fun human_of_formula (A (id,pl)) = 
  let val opers = human_of_id id in
    if null pl then opers else
    if !infix_flag andalso length pl = 2 andalso fst id <> 6
    then "(" ^ human_of_formula (hd pl) ^ " " ^ opers ^ " " ^
               human_of_formula (hd (tl pl)) ^ ")"
    else "(" ^ String.concatWith " " (opers :: map human_of_formula pl) ^ ")"
  end

val formula_of_human = sexp_to_formula o string_to_sexp  

(* -------------------------------------------------------------------------
   Debugging
   ------------------------------------------------------------------------- *)

val fh = formula_of_human
val hf = human_of_formula
fun hfc tml = "(" ^ String.concatWith " " (map hf tml) ^ ")";
val pe = print_endline
val dbg_flag = ref false
val dbg_level = ref 0
fun dbg n f = 
  if !dbg_flag then 
    if n <= !dbg_level 
    then pe (String.concat (List.tabulate(n, fn _ => "  ")) ^ f ())
    else ()
  else ()

(* -------------------------------------------------------------------------
   Substitution
   ------------------------------------------------------------------------- *)
 
fun subst_one (v,p) (A (i,pl)) = 
  (
  checktimer ();
  if i = v then p 
  else if i = compr_id then A (i, hd pl :: map (subst_one (v,p)) (tl pl))
  else if i = loop_id then A (i, hd pl :: map (subst_one (v,p)) (tl pl))
  else if mem i [loop2_id, loop2h_id] then 
    let val (al,bl) = part_n 2 pl in A (i, al @  map (subst_one (v,p)) bl) end
  else A (i, map (subst_one (v,p)) pl)
  )

fun substl vpl (A (i,pl)) = 
  (
  checktimer ();
  case List.find (fn (a,b) => i = a) vpl of SOME (a,b) => b | NONE =>
    (
    if i = compr_id then A (i, hd pl :: map (substl vpl) (tl pl))
    else if i = loop_id then A (i, hd pl :: map (substl vpl) (tl pl))
    else if mem i [loop2_id, loop2h_id] then 
      let val (al,bl) = part_n 2 pl in A (i, al @  map (substl vpl) bl) end
    else A (i, map (substl vpl) pl)
    )
  )
  
end
