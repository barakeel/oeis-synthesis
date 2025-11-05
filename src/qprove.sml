(* ========================================================================= *)
(* DESCRIPTION   : Theorem prover                                            *)
(* ========================================================================= *)

structure qprove :> qprove = struct

open HolKernel Abbrev boolLib aiLib kernel qsubst sexp
val ERR = mk_HOL_ERR "qprove"

type prog = kernel.prog
type formula = kernel.prog
type qprove = (formula list * (prog * int))
type state = prog list
type exec = state * state -> state 

exception Proof
exception Error

val dbg_flag = ref false
fun dbg f = if !dbg_flag then f () else ()

(* idea: 
1) list of list of formulas: hd2 tl2 push2, 
2) let the LM program the outer loop 
3) add skolemization, 
clausing goals by unification or matching
rewriting using unification or matching
4) add splitting as a primitive returning the theorem A \/ B
*)

(* rewrite rule *)
(* need a rebuild function *)

datatype obj = Thm of formula list * int | Term of formula

val not_id = 0
val or_id = 1
val forall_id = 2
val eq_id = 3

fun error () = raise Error

fun next obj = case obj of
    Thm (x,i) :: m => Thm (x,i+1) :: m
  | _ => error ()

fun is_eq (Ins(id,_)) = id = eq_id

fun find_nth test n l = case l of 
    [] => NONE
  | a :: m => 
    if not (test a) then find_nth test n m else
    if n <= 0 then SOME a else find_nth test (n-1) m

(* todo: add unification *)
fun rw_match obj1 obj2 = case (obj1,obj2) of
      (Thm (litl1,i1) :: m1, Thm(litl2,i2) :: m2) => 
      (
      case find_nth is_eq i1 litl1 of 
        SOME (Ins (3,[t1,t2])) => Thm (rwl_pos (t1,t2) (litl2,i2), 0) :: m2
      | _ => error ()
      )
    | _ => error ()

end (* struct *)

(*
dbg (fn () => pe ("rewrite " ^ String.concatWith " " (map hf tml2) 
     ^ " with " ^ hf eq));
clauses are set
*)

(*
datatype term = Ins of int * term list

fun rewrite (term,i) 


val t =
  Ins("f", [Ins("a", []), Ins("b", []), Ins("g", [Ins("a", [])])])

val SOME (subtm,rebuild) =
  find_nth_subterm (fn Ins(id, _) => id = "a") 1 t
(* the second "a" *)

val new_term = rebuild (Ins("x", []))
(* result: Ins("f", [Ins("a", []), Ins("b", []), Ins("g", [Ins("x", [])])]) *)


fun nth_tml test buildf tml n = case tml of
    [] => NONE
  | tm :: m =>
    case 

fun nth test buildf (Ins(id,tml) as tm, n) =
  if test tm then 
    if n <= 0 
      then SOME (tm, buildf)
      else 
         
  
           
fun rewrite eq thm = case (eq,thm) of
    (Thm (tml1,i1) :: _, Thm (tml2,i2) :: m) =>
    case find_nth_eq thml1 i1 of
        NONE => error ()
      | SOME eq => 
      (

      Thm (map (rewrite_match (eq,thm)) ,_) :: m
      )
      else error ()
    end
  | _ => error () 

datatype object = Thm of formula list | Term of formula

(* strip forall before applying or/and conj maybe no distinction between or
or conj automatic skolemization *)

fun tmem g gl = exists (fn x => prog_compare (g,x) = EQUAL) gl

fun merge_goal gl1 gl2 =
  let val gl2' = filter (fn x => not (tmem x gl1)) gl2 in
    gl1 @ gl2'
  end

(* more general term is on the left *)

Thm, index, next, down (moving the pointer)

destruct (actually destruct at the pointer location)
traverse term (go through all the subterms and produce something)
push
catch_error then () else

fun f 

(* should my clause be represented by an array *)
fun next_clause (Thm(gl1a,gl1b)) = Thm (hd gl1b :: gl1a, tl gl1b)

(* 
necessary to tell where the rewrite could happen, series of instruction 
maybe should make them unfailing
*)

fun down (Thm(gl1a,i,l)) = Thm (gl1a,i,1::l) (* the second field is the 


fun resolve_match (Thm(gl1a,gl1b),Thm(gl2a,gl2b)) = 
  let 
    fun f b = if b then map inst_aux gl1 else error () 
    val newgl1 = with_match (thm1, neg thm2) f
    val newgl = merge_goal gl2 newgl1 
  in
    case newgl of
      [] => raise Proof
    | g :: m => Thm (g,m)
  end

fun resolve_unify (Thm (thm1,gl1)) (Thm (thm2,gl2)) = 
  let 
    fun f b = if b then (map inst_aux gl1, map inst_aux gl2) else error () 
    val (newgl1,newgl2) = with_unify (thm1, neg thm2) f
    val newgl = merge_goal newgl2 newgl1 
  in
    case newgl of
      [] => raise Proof
    | g :: m => Thm (g,m)
  end

(* 
generalize the resolve tactic later to look for literals that could match 
in the other theorem collect literals 
*)


(* to do maybe checks that free variables are *)
fun forall thm = case thm of
    Thm (Ins(2,[v,body]), gl) :: m => body :: m
  | _ => error ()

fun orl x = case x of
    Thm (Ins(1,[a,b]), gl) :: m => Thm (a, b::gl) :: m
  | _ => error ()

fun orr x = case x of
    Thm (Ins(1,[a,b]), gl) :: m => Thm (b, a::gl) :: m
  | _ => error ()

fun conjl x = case x of 
    Thm (Ins(0,Ins(1,[a,b])),gl) :: m => Thm (Ins(0,a),gl) :: m
  | _ => error ()
  
fun conjr x = case x of 
    Thm (Ins(0,Ins(1,[a,b])),gl) :: m => Thm (Ins(0,b),gl) :: m
  | _ => error ()

fun forall thmtop ttop = case (thmtop,ttop) of
    (Thm (Ins(2,[v,body]),gl) :: m, Term t :: _) => 
    if is_predicate_level t then error () else 
    Thm (subst (v,t) body, gl) :: m
  | _ => error ()

fun free_vars_aux bset fset tm = case tm of
    Ins(2,[v,body]) => free_vars_aux (eadd v bset) body  
  | Ins(id,argl) => 
    (
    if is_var id andalso not (emem id bset) 
    then fset := eadd id (!fset)
    else (); 
    app (free_vars_aux bset fset argl)
    )
  
fun free_vars term = 
  let 
    val bset = eempty Int.compare 
    val fset = ref (eempty Int.compare)
    val _ = free_vars_aux bset fset tm
  in
    elist (!fset)
  end
  
fun exists objl = case objl of
    Thm (Ins(0,[Ins(2,[v,body])]) as tm, gl) :: m =>
    Thm (neg (subst (v, Ins (fresh_const (), free_vars tm)) body),gl) :: m
  | _ => error ()



(*
(* useful if the input is not in the cnf format *)
fun cnf term = case term of
    Ins(0,Ins(1,[a,b]) => List.concat [cnf (neg a), cnf (neg b)]
  | Ins(1,[a,b]) => 
    let val (cnfal,cnfbl) = (cnf a, cnf b) in
       map mk_or (cartesian_product cnfal cnfbl)
     end            
  | Ins(2,[v,body]) => cnf body 
    (* assumes variables no conflict between variables *)
  | Ins(0,[Ins(2,[v,body])]) => cnf
    (neg (subst (v, Ins (fresh_const (), free_vars term)) body))
  | literal => [literal]
*)

(a,bl)
(c,bl) 
- pointer_eq on the list instead of just testing each goals individually
- pointer_eq on the goals before testing equality other wise
- quadratic merge (potentially factoring)


fun orl x = case x of
    Thm (Ins(1,[a,b]), gl) :: m => Thm (a, b::gl) :: m
  | _ => error ()

fun orr x = case x of
    Thm (Ins(1,[a,b]), gl) :: m => Thm (b, a::gl) :: m
  | _ => error ()

fun conjl x = case x of 
    Thm (Ins(0,Ins(1,[a,b])),gl) :: m => Thm (Ins(0,a),gl) :: m
  | _ => error ()
  
fun conjr x = case x of 
    Thm (Ins(0,Ins(1,[a,b])),gl) :: m => Thm (Ins(0,b),gl) :: m
  | _ => error ()

fun forall thmtop ttop = case (thmtop,ttop) of
    (Thm (Ins(2,[v,body]),gl) :: m, Term t :: _) => 



(* destruct term *)
fun dest x = case x of 
    Thm (Ins(_,l),_) :: m => map Term l @ m
  | Term (Ins(_,l)) :: m => map Term l @ m


(* -------------------------------------------------------------------------
   Human interface
   ------------------------------------------------------------------------- *) 

val humanv = Vector.fromList ["not","or","forall","=","0","suc","+"]
val humand = dnew String.compare (number_snd 0 (vector_to_list humanv));

fun id_of_oper s = 
  if hd_string s = #"v" 
  then ~ (string_to_int (tl_string s))
  else dfind s humand;
  
val zero_id = id_of_oper "0";
val suc_id = id_of_oper "suc";
val zero = Ins(zero_id,[])
fun suc t = Ins(suc_id,[t])
  
fun mk_nat i = 
  if i < 0 then raise ERR "mk_nat" "negative"
  else if i = 0 then Ins (zero_id,[])
  else suc (mk_nat (i-1))
  
fun sexp_to_formula phi = case phi of
    Atom s => if Char.isDigit (hd_string s) 
              then mk_nat (string_to_int s)
              else Ins (id_of_oper s,[])
  | Sexp (Atom s :: argl) => Ins (id_of_oper s, map sexp_to_formula argl)
  | _ => raise ERR "sexp_to_formula" "";

fun human_formula (Ins (i,pl)) = 
  let val opers = 
    if i < 0 then "v" ^ its (~i) else
    if i >= Vector.length humanv then "f" ^ its i else 
    Vector.sub (humanv,i) 
  in
    if null pl then opers else
    "(" ^ String.concatWith " " (opers :: map human_formula pl) ^ ")"
  end

val formula_human = sexp_to_formula o string_to_sexp  

(* -------------------------------------------------------------------------
   Timer
   ------------------------------------------------------------------------- *)
   
fun timed_after y = 
  (
  incr abstimer;    
  if !abstimer > !timelimit then raise ProgTimeout else y
  )

fun timed_prog_compare (Ins x,Ins y) =
  (
  incr abstimer;
  cpl_compare Int.compare (list_compare timed_prog_compare) (x,y)
  )
  
fun occurences term (formula as (Ins(id,l))) = 
  if timed_prog_compare (formula,term) = EQUAL 
  then 1
  else sum_int (map (occurences term) l);
  
    
fun timed_var opf fl = case fl of 
    [] => (fn x => timed_after (opf x))
  | _ => raise ERR "timed_var" ""
  
fun timed_nullary opf fl = case fl of
    [] => (fn x => timed_after (opf ()))
  | _ => raise ERR "timed_nullary" ""
  
fun timed_unary opf fl = case fl of
    [f1] => (fn x => timed_after (opf (f1 x)))
  | _ => raise ERR "timed_unary" ""

fun timed_binary opf fl = case fl of
    [f1,f2] => (fn x => timed_after (opf (f1 x) (f2 x)))
  | _ => raise ERR "timed_binary" ""

(* -------------------------------------------------------------------------
   Two variables
   ------------------------------------------------------------------------- *)

fun varx (x,y) = x
fun vary (x,y) = y

val timed_varx = timed_var varx
val timed_vary = timed_var vary

(* -------------------------------------------------------------------------
   List operations
   ------------------------------------------------------------------------- *)

fun list_hd a = case a of e :: m => [e] | _ => error ()
fun list_tl a = case a of e :: m => m | _ => error ()
fun list_push a b = case a of e :: m => e :: b | _ => error ()
fun list_null () = []

val timed_hd = timed_unary list_hd
val timed_tl = timed_unary list_tl
val timed_push = timed_binary list_push
val timed_null = timed_nullary list_null

(* -------------------------------------------------------------------------
   Control flow
   ------------------------------------------------------------------------- *)

fun timed_cond fl = case fl of
    [f1,f2,f3] => 
    (fn x => timed_after (if null (f1 x) then f2 x else f3 x))
  | _ => raise ERR "timed_cond" ""

fun can_error f x = ((ignore f x; true) handle Error => false)

fun timed_cond_error fl = case fl of
    [f1,f2,f3] => 
    (fn x => timed_after (if can_error f1 x then f2 x else f3 x))
  | _ => raise ERR "timed_cond_error" ""


fun while_aux f g x y =
  if null x then y else while_aux f g (f (x,y)) (g(x,y))

fun timed_while fl = case fl of
    [f1,f2,f3,f4] =>
    (fn x => timed_after (while_aux f1 f2 (f3 x) (f4 x)))
  | _ => raise ERR "timed_while" ""
  
(* -------------------------------------------------------------------------
   Minimal syntax
   ------------------------------------------------------------------------- *)

(* propositional *)
val not_id = 0
val or_id = 1

(* first-order *)
val forall_id = 2
val equal_id = 3
fun is_predicate_level (Ins(id,_)) = id >= 0 andalso id <= 3

(* arithmetic *)
val zero_id = 4
val suc_id = 5
val add_id = 6

(* other constants/functions predicates: 5 and up *)
fun var id = if id < 0 then Ins (id,[]) else raise ERR "var" ""
fun neg f = case f of
    Ins (not_id,[g]) => g
  | _     => Ins (not_id,[f])
fun or a b = Ins (or_id,[a,b])
fun forall v body = Ins (forall_id,[v,body])

val fresh_const_id = ref 0
fun fresh_const () = let val v = var (!fresh_const_id) 
  in incr fresh_const_id; v end

(* tests: term/thm -> bool(0/1) *)
fun is_v (Ins(i,_)) = i < 0
fun is_not (Ins(i,_)) = i = not_id
fun is_or (Ins(i,_)) = i = or_id
fun is_forall (Ins(i,_)) = i = forall_id
fun is_equal (Ins(i,_)) = i = equal_id
fun equal_term (a,b) = prog_compare (a,b) = EQUAL

(* constructors *)
fun mk_forall (var,body) = Ins(forall_id, [var,body])
fun mk_equal (t1,t2) = Ins(equal_id,[t1,t2])
val zero = Ins(zero_id,[])
fun suc t = Ins(suc_id,[t])
fun mk_add (t1,t2) = Ins(add_id,[t1,t2])

val fh = formula_human
val axiom1 = fh "(forall v1 (= v1 v1))"
val axiom2 = fh "(forall v1 (= (+ v1 0) v1))"
val axiom3 = fh "(forall v1 (forall v2 (= (+ v1 (suc v2)) (suc (+ v1 v2)))))"

(* destructors *)
fun dest_ins (Ins(id,l)) = (id,l) 
fun get_id f = fst (dest_ins f)
fun get_arg f = snd (dest_ins f)

fun all_varid_aux acc f = case f of
    Ins(i,[]) => if i < 0 then acc := i :: !acc else ()
  | Ins(_,l) => app (all_varid_aux acc) l
  
fun all_varid f = let val acc = ref [] in all_varid_aux acc f; !acc end

fun subst_aux (itop,f) ftop = case ftop of
    Ins(i,[]) => if i = itop then f else ftop
  | Ins(i,l) => Ins(i, map (subst_aux (itop,f)) l)
  
fun subst (v,f) ftop = subst_aux (get_id v,f) ftop 

(* -------------------------------------------------------------------------
   Term operations
   ------------------------------------------------------------------------- *)

fun same_id x y = case (x,y) of
    (Ins (i1,_) :: _, Ins (i2,_) :: _) => if i1 = i2 then x else []
  | _ => error ()mateurs puissent si tu regardes les positions des joueurs pendant leurs tirs et leur passes tu vois que c'est quand mê

fun test_wrap test x = case x of 
    t :: m => if test t then x else []
  | _ => error ()

val timed_is_v = timed_unary (test_wrap is_v)
val timed_is_not = timed_unary (test_wrap is_not)
val timed_is_or = timed_unary (test_wrap is_or)
val timed_same_id = timed_binary same_id


val timed_dest = timed_unary dest

(* -------------------------------------------------------------------------
   Branch insertion: add a new fact to the branch
   ------------------------------------------------------------------------- *)

(* there is only one local theorem per branch, the one that started
   the branch, (could be referred to as local_thm or x) 

goal list * term list * term list ->
goal list * term list * term list

(* need rules and tactics *)
rewrite (thm1 thm2) produces a new theorem
rewrite_tac (thm1)  (expects a theroem) 
  produces a new goal (forget about the old one)


commands affect the (local_thm:goal) (i.e. part of the state)
by either rewriting it splitting it.   
*)

fun is_negrefl tm = case tm of
    Ins(0,[Ins(3,[t1,t2])]) =>
    prog_compare (t1,t2) = EQUAL     
  | _ => false

fun insert f (br as {have, havel, pending}) =
  if emem f have then SOME br
  else if is_negrefl f orelse emem (neg f) have then NONE
  else SOME {have = eadd f have, havel = f :: havel, pending = f :: pending}

fun insert_list fl br = case fl of 
    [] => SOME br
  | f :: m => 
    (
    case insert f br of 
      NONE => NONE
    | SOME br' => insert_list m br'
    )

(* -------------------------------------------------------------------------
   Branch expansion
   ------------------------------------------------------------------------- *)

val hf = human_formula
fun pe x = (append_endline (selfdir ^ "/qprove_dbg") x; print_endline x)

fun expand_or l br0 brm = 
   let val newbrl = List.mapPartial (C insert br0) l in
     newbrl @ brm
   end

fun expand_bro bro brm = case bro of
    NONE => brm
  | SOME br => (br :: brm)

fun expand_and l br0 brm = expand_bro (insert_list (map neg l) br0) brm

fun expand_exists (v,body) br0 brm = 
  let val newf = neg (subst (v, fresh_const ()) body) in
    expand_bro (insert newf br0) brm
  end
  
fun expand_forall (v,body) instancel br brm =
  let val rl =
    if null instancel then [] else
    let 
      val instance = hd instancel 
    in
      if is_predicate_level instance then [] else 
      let 
        val r = subst (v,instance) body
        val _ = dbg (fn () =>  
         pe ("forall: " ^ hf body ^ " at " ^ hf v ^  " -> " ^ hf r))      
      in
        [r]
      end 
    end
  in
    expand_bro (insert_list rl br) brm
  end

(*
todo improve rewrite to do matching on universal variables 
use some range of positive numbers for skolem constants
only allow rewrite with the original theorems (not the deduced ones?)
store theorems to be access in a database (list of theorems)
axiom1 axiom2 axiom3 as primitives?
*)

fun rewrite_aux pos (t1,t2) (t as Ins(id,l))= 
  if !pos < 0 then t else
  if timed_prog_compare (t,t1) = EQUAL 
  then 
    (
    decr pos; 
    if !pos < 0 then t2 else Ins (id, map (rewrite_aux pos (t1,t2)) l)
    )
  else 
    Ins (id, map (rewrite_aux pos (t1,t2)) l)


fun strip_forall formula = case formula of
    Ins(2,[v,body]) => strip_forall body  
  | _ => formula

fun rewrite have form eql = case eql of [] => [] | qeq :: m =>
   if not (emem qeq have) then [] else
   let val eq = strip_forall (hd eql) in
     dbg (fn () => pe ("rewrite: " ^ hf form ^ " with " ^ hf eq));
     [rewrite_match (eq,form)]
   end

fun expand_rewrite have formula eql br brm = 
  let val formulal = rewrite have formula eql in
    expand_bro (insert_list formulal br) brm
  end


   
(* positional rewrite rule *)   


   
   | _ => error ()
   if not (emem qeq have) then [] else
   let val eq = strip_forall (hd eql) in
     dbg (fn () => pe ("rewrite: " ^ hf form ^ " with " ^ hf eq));
     [rewrite_match (eq,form)]
   end
  
  
  Ins(2,[v,body]) =>
          let val br' = {have = have, havel = havel, pending = fm @ [f]} in
            expand_forall (v,body) [] br' brm (* replace [] by instancel *)
          end
        | Ins(0,[Ins(2,[v,body])]) => 


fun expand_branch {have, havel, pending} instancel brm =
  case pending of
      [] => raise ERR "expand_branch" "empty pending"
    | f :: fm =>
      let 
        val br = {have = have, havel = havel, pending = fm}  
      in
        case f of
          Ins(1,l) => 
          (
          dbg (fn () =>  pe ("or: " ^ hf f));
          expand_or l br brm
          )
        | Ins(0,[Ins(1,l)]) => 
          (
          dbg (fn () => pe ("and: " ^ hf f));
          expand_and l br brm
          )
        | Ins(2,[v,body]) =>
          let val br' = {have = have, havel = havel, pending = fm @ [f]} in
            expand_forall (v,body) [] br' brm (* replace [] by instancel *)
          end
        | Ins(0,[Ins(2,[v,body])]) => 
          (
          dbg (fn () =>  pe ("exists: " ^ hf f));
          expand_exists (v,body) br brm
          )
        | _ => 
          let val br' = {have = have, havel = havel, pending = fm @ [f]} in
            expand_rewrite have f instancel br' brm
          end
      end

fun drop_pending ({have, havel, pending}: branch) =
  {have = have, havel = havel, pending = tl pending @ [hd pending]}

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val action_flag = ref false
val actionf_glob = ref (fn (_ : branch) => []) 

fun search br brm = 
  (
  incr abstimer;
  if null (#pending br) then false else 
  if not (!action_flag) then 
    (
    case expand_branch br [] brm of
      [] => true (* unsatisfiable *)
    | newbr :: newbrm => search newbr newbrm
    )
  else
    case (!actionf_glob) br of
      [] => search (drop_pending br) brm
    | terml =>
      (
      case expand_branch br terml brm of
          [] => true (* unsatisfiable *)
        | newbr :: newbrm => search newbr newbrm
      )
  )
 
fun refute premises =
  let 
    val _ = dbg (fn () => app pe (["start proof","start premises"] @ 
      (map hf premises) @ ["end premises"]))
    val start = {have = eempty timed_prog_compare, havel = [], pending = []}
    val vl = List.concat (map all_varid premises)
    val _ = fresh_const_id := 1000 (* high *)
    val r = 
    let val r' = 
            (
            case insert_list premises start of
              NONE => true
            | SOME br => search br []
            )
      in
        if r' then dbg (fn () => pe "unsat") 
              else dbg (fn () => pe "unknown"); 
        r'
      end
        handle Error => (dbg (fn () => pe "error"); false) 
             | ProgTimeout => (dbg (fn () => pe "timeout"); false)
    val _ = dbg (fn () => pe ("abstract time: " ^ its (!abstimer)))
    val _ = dbg (fn () => pe "end proof")
      
  in
    r
  end

fun prove premises conjecture = refute ((neg conjecture) :: premises)

(* -------------------------------------------------------------------------
   Programming primitives
   ------------------------------------------------------------------------- *)

val timedv = Vector.fromList 
  [timed_varx, timed_vary,
   timed_hd, timed_tl, timed_push, timed_null,
   timed_is_v, timed_is_not, timed_is_or, timed_same_id, timed_dest,
   timed_cond, timed_while]

fun mk_exec (Ins (id,pl)) = Vector.sub (timedv,id) (map mk_exec pl)

val error_count = ref 0
val timeout_count = ref 0
val sat_count = ref 0
val unsat_count = ref 0

fun qprove p (phi,tim) = 
  let 
    val exec = mk_exec p
    val _ = abstimer := 0
    val _ = timelimit := tim
    fun f br = exec (#pending br, #havel br)
    val _ = action_flag := true
    val _ = actionf_glob := f 
    val b = 
      let val b' = prove [] phi in
        if b' then incr unsat_count else incr sat_count; b'
      end

  in 
    (b,!abstimer)
  end

fun qprove_asm p ((asm,phi),tim) = 
  let 
    val exec = mk_exec p
    val _ = abstimer := 0
    val _ = timelimit := tim
    fun f br = exec (#pending br, #havel br)
    val _ = action_flag := true
    val _ = actionf_glob := f 
    val b = 
      let val b' = prove asm phi in
        if b' then incr unsat_count else incr sat_count; b'
      end
  in 
    (b,!abstimer)
  end

fun qprove_baseline phi = 
  let 
    val _ = abstimer := 0
    val _ = action_flag := false
    val b = prove [] phi
  in 
    (b,!abstimer)
  end;

(* -------------------------------------------------------------------------
   Parse entailment examples
   ------------------------------------------------------------------------- *)

fun parse_ex s =
  let
    fun is_comma c = c = #","
    val (s1,s2,s3) = triple_of_list (first_n 3 (String.tokens is_comma s))
    fun translate_token c = case c of
        #">" => " ==> "
      | #"|" => " \\/ "
      | #"&" => " /\\ "
      | #"~" => "~ "
      | #"(" => "("
      | #")" => ")"
      | _ => if Char.isLower c
             then ("(V" ^ Char.toString c ^ ":bool)")
             else raise ERR "translate_token" ""
    fun dm_to_hol s =
       let val s' = String.translate translate_token s in
         (Parse.Term [HOLPP.QUOTE s']
          handle HOL_ERR _ => raise ERR "read_ex" s')
       end
  in
    (mk_imp (dm_to_hol s1, dm_to_hol s2), [Real.fromInt (string_to_int s3)])
  end;

fun read_true_exl file =
  let
    val exl1 = map parse_ex (readl file)
    val exl2 = map fst (filter (fn (_,x) => hd x > 0.5) exl1)
  in
    map rename_allvar exl2
  end

fun read_false_exl file =
  let
    val exl1 = map parse_ex (readl file)
    val exl2 = map fst (filter (fn (_,x) => hd x < 0.5) exl1)
  in
    map rename_allvar exl2
  end

fun htt t = 
  if is_var t then 
    Ins (~1 - (string_to_int (tl_string (fst (dest_var t)))),[])
  else if is_neg t then neg (htt (dest_neg t))
  else if is_disj t then 
    let val (a,b) = dest_disj t in or (htt a) (htt b) end
  else if is_conj t then
    let val (a,b) = dest_conj t in neg (or (neg (htt a)) (neg (htt b))) end
  else if is_imp t then
    let val (a,b) = dest_imp t in or (neg (htt a)) (htt b) end
  else raise ERR "htt" "" ;


(* -------------------------------------------------------------------------
   Input/output
   ------------------------------------------------------------------------- *) 
  
fun apply_move_formula move board =
  let 
    val arity = if move = 0 then 1 else if move = 1 then 2 else 0
    val (l1,l2) = part_n arity board 
  in
    if length l1 <> arity 
    then raise ERR "apply_move" "arity"
    else Ins (move, rev l1) :: l2
  end 

fun prog_of_tokenl tokenl = 
  let val progl = foldl (uncurry apply_move_formula) [] tokenl in
    case progl of [p] => p | _ => raise ERR "prog_of_tokenl" "not a singleton"
  end;

fun string_of_formula p = ilts (tokenl_of_prog p);
fun formula_of_string s = prog_of_tokenl (stil s);

fun human_qprove_one (formulal,(p,i)) = 
   String.concatWith "|"
    [String.concatWith "," (map human_formula formulal), 
     human.human_trivial p, its i]

fun write_qprove_one (formulal,(p,i)) = 
  String.concatWith "|"
    [String.concatWith "," (map string_of_formula formulal), 
     gpt_of_prog p, its i]

fun write_qprove file l = writel file (map write_qprove_one l)

fun read_qprove_one s = 
  let 
    val (s1,s2,s3) = triple_of_list (String.tokens (fn x => x = #"|") s)
    val sl1 = String.tokens (fn x => x = #",") s1
  in
    (map formula_of_string sl1, (prog_of_gpt s2, string_to_int s3))
  end

fun read_qprove file = map read_qprove_one (readl file)

(* -------------------------------------------------------------------------
   SAT solving benchmark
   ------------------------------------------------------------------------- *)

fun create_benchmark8 name easyl =    
  let  
    val () = 
      if length (mk_fast_set prog_compare easyl) <> length easyl 
      then raise ERR "create_benchmark" "not a set" else ()
    val easyl2 = mk_batch 2 (shuffle (easyl @ easyl));
    val easyl4 = mk_batch 4 (List.concat (shuffle (easyl2 @ easyl2)));
    val easyl8 = mk_batch 8 (List.concat (shuffle (easyl4 @ easyl4)));
    val easyl8' = List.concat easyl8
  in
    writel (selfdir ^ "/data/" ^ name) (map string_of_formula easyl8')
  end
  
(*
load "qprove"; load "game"; load "human"; 
open qprove; open kernel aiLib;
val ERR = mk_HOL_ERR "test";
val dir = "/home/thibault/logical-entailment-dataset/data";
val filel = listDir dir;
val orgl = read_true_exl (dir ^ "/test_easy.txt");
val easyl = map htt orgl;
create_benchmark8 "entail_easyl8" easyl;
*)
  
(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *) 

val qproved_glob = ref (dempty (list_compare prog_compare))
val formulal_glob = ref []

fun checkinit_qprove () = qproved_glob := dempty (list_compare prog_compare)

fun update_qproved (formulal,(p,sc)) = 
  let
    fun upd () = qproved_glob := dadd formulal (p,sc) (!qproved_glob)
  in
    case dfindo formulal (!qproved_glob) of
      NONE => upd ()
    | SOME (oldp,oldsc) => 
      if sc > oldsc 
        then () 
      else if sc = oldsc andalso prog_compare_size (oldp,p) <> GREATER 
        then ()
      else upd ()
  end

fun checkfinal_qprove () = dlist (!qproved_glob) 

fun score_one (b,tim) = if not b then (b,2 * !timelimit) else (b,tim)

fun init_formulal_glob () = 
  let 
    val formulal = 
      map formula_of_string (readl (selfdir ^ "/data/entail_easyl8"))
    fun scoreo (b,tim) = if not b then raise ERR "score" "" else tim
    val formulaltim = map_assoc (scoreo o qprove_baseline) formulal
    val _ = print_endline ("initialized " ^ its (length formulal) ^ " formulas")
  in
    formulal_glob := mk_batch 8 formulaltim
  end
  
fun checkonline_qprove p = 
  let 
    val _ = if null (!formulal_glob) 
            then raise ERR "checkonline_qprove" "empty"
            else ()
    val formulaltop = random_elem (!formulal_glob)
    val rl = map_assoc (score_one o qprove p) formulaltop
    val rl8 = [rl]
    val rl4 = mk_batch 4 rl
    val rl2 = mk_batch 2 rl
    val rl1 = mk_batch 1 rl
    fun g x = 
      let 
        val (formulaltim,scl) = split x 
        val formulal = map fst formulaltim
      in
        if not (exists fst scl) then () else
        let val sc = sum_int (map snd scl) + prog_size p in
          update_qproved (formulal,(p,sc))
        end
      end
  in
    app g (rl8 @ rl4 @ rl2 @ rl1)
  end 

fun merge_qprove newl fileo = 
  let 
    val _ = checkinit_qprove ()
    val oldl = if isSome fileo then read_qprove (valOf fileo) else []
  in
    app update_qproved (newl @ oldl);
    checkfinal_qprove ()
  end

(* -------------------------------------------------------------------------
   Example: arithmetic
   ------------------------------------------------------------------------- *)

(*

load "qprove"; load "game"; open qprove; open kernel aiLib;
val ERR = mk_HOL_ERR "test";

fun loop formula n maxn = 
  if n >= maxn then NONE else
  let 
    val p = game.random_prog 12
    val (b,t) = qprove_asm p (([axiom2,axiom3],formula),1000)
  in
    if b then SOME (p,t,n) else loop formula (n+1) maxn 
  end;
  
fun loopw formula maxn =   
  let 
    val (ro,topt) = add_time (loop formula 0) maxn 
    val _ = print_endline ("total time: " ^ rts_round 2 topt)
  in
    case ro of 
      NONE => (print_endline "failure"; NONE)
    | SOME (p,t,n) => 
      (
      print_endline ("program: " ^ human.human_trivial p); 
      print_endline ("program time: " ^ its t);
      print_endline ("tries: " ^ its n);
      SOME (p,t,n)
      )
  end;

fun get_proof phi limit =
  let
    val _ = dbg_flag := false;
    val (p,t,n) = valOf (loopw phi limit);
    val _ = dbg_flag := true;
    val _ = erase_file (selfdir ^ "/qprove_dbg");
    val _ = qprove_asm p (([axiom2,axiom3],phi),1000)
  in
    ()
  end;

val formula = formula_human "(= (+ 1 1) 2)";
val formula = formula_human "(= (+ 1 2) 3)";

val formula = formula_human "(= (+ 3 3) 6)";

get_proof formula 10000000;

loopw formula2 1000000;


val f1 = formula_human "(not (= (+ 0 (suc 0)) (suc 0)))";
val f2 = formula_human "(+ 0 (suc 0))";
occurences f2 f1;

x + s(y) = s(x + y)

0 + s(0) <> s(0)

0 + s(0) = s(0 + 0) (* instantiate match *)

s(0+0) = s(0)
*)


 *)*)
 
 


