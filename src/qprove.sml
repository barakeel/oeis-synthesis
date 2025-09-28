(* ========================================================================= *)
(* DESCRIPTION   : Theorem prover                                            *)
(* ========================================================================= *)

structure qprove :> qprove = struct

open aiLib kernel
val ERR = mk_HOL_ERR "qprove"

type prog = kernel.prog

(*
1) return type should be a list and the first element of the list
that is an integer should be the result if > 0 then 1 else 0
is multiplication by 0 and 1 allowed?

2) train on the shortest/fastest programs.
*)

type state = prog list
type exec = state * state -> state 
exception Error


(* -------------------------------------------------------------------------
   Timer
   ------------------------------------------------------------------------- *)
   
fun timed_after y = 
  (
  incr abstimer;    
  if !abstimer > !timelimit then raise ProgTimeout else y
  )

fun timed_var opf = (fn x => timed_after (opf x))

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

fun list_hd a = case a of e :: m => [e] | _ => raise Error 
fun list_tl a = case a of e :: m => m | _ => raise Error 
fun list_push a b = case a of e :: m => e :: b | _ => raise Error

val timed_hd = timed_unary list_hd
val timed_tl = timed_unary list_tl
val timed_push = timed_binary list_push

(* -------------------------------------------------------------------------
   Control flow
   ------------------------------------------------------------------------- *)

fun timed_cond fl = case fl of
    [f1,f2,f3] => 
    (fn x => timed_after (if null (f1 x) then f2 x else f3 x))
  | _ => raise ERR "timed_cond" ""

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

(* higher-order *)
val app_id = 3
val lambda_id = 4

(* other constants/functions predicates: 5 and up *)
fun var id = Ins (id,[])
fun neg f = case f of
    Ins (not_id,[g]) => g
  | _     => Ins (not_id,[f])
fun or a b = Ins (or_id,[a,b])
fun forall v body = Ins (forall_id,[v,body])
val fresh_var_id = ref (~1)
fun fresh_var () = let val v = var (!fresh_var_id) in decr fresh_var_id; v end

(* tests: term/thm -> bool(0/1) *)
fun is_var (Ins(i,_)) = i < 0
fun is_not (Ins(i,_)) = i = not_id
fun is_or (Ins(i,_)) = i = or_id
fun is_forall (Ins(i,_)) = i = forall_id
fun equal_term (a,b) = prog_compare (a,b) = EQUAL

(* destructors *)
fun dest_ins (Ins(id,l)) = (id,l) 
fun get_id f = fst (dest_ins f) (* maybe not necessary *)
fun get_arg f = snd (dest_ins f)

(* others *)
fun non_lit f =  case f of
    Ins(1,_) => true
  | Ins(0,[Ins(1,_)]) => true
  | _ => false
  
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
  | _ => raise Error

fun test_wrap test x = case x of 
    t :: m => if test t then x else []
  | _ => raise Error

val timed_is_var = timed_unary (test_wrap is_var)
val timed_is_not = timed_unary (test_wrap is_not)
val timed_is_or = timed_unary (test_wrap is_or)
val timed_same_id = timed_binary same_id

(* -------------------------------------------------------------------------
   Branch insertion: add a new fact to the branch
   ------------------------------------------------------------------------- *)

type branch = {have : prog Redblackset.set, pending : prog list}

fun insert f (br as {have, pending}) =
  if emem (neg f) have then NONE else
  if emem f have then SOME br else
    SOME {have = eadd f have, 
          pending = if non_lit f then f :: pending else pending}

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

fun expand_or l br0 brm = 
   let val newbrl = List.mapPartial (C insert br0) l in
     newbrl @ brm
   end

fun expand_bro bro brm = case bro of
    NONE => brm
  | SOME br => (br :: brm)

fun expand_and l br0 brm = expand_bro (insert_list (map neg l) br0) brm

fun expand_exists (v,body) br0 brm = 
  let val newf = neg (subst (v, fresh_var ()) body) in
    expand_bro (insert newf br0) brm
  end
  
fun expand_forall (v,body) instance br0 brm =
  let val newf = subst (v,instance) body in
    expand_bro (insert newf br0) brm
  end

fun expand_branch ({have, pending}: branch) (brm: branch list) = case pending of
      [] => raise ERR "expand_branch" "empty pending"
    | f :: fm =>
      let val br0 = {have = have, pending = fm} in
        case f of
          Ins(1,l) => expand_or l br0 brm
        | Ins(0,[Ins(1,l)]) => expand_and l br0 brm
        | Ins(0,[Ins(2,[v,body])]) => expand_exists (v,body) br0 brm
        | _ => raise ERR "expand_branch" "unexpected"
      end
      
fun expand_branch_forall (br0: branch) instance brm = case #pending br0 of
      [] => raise ERR "expand_branch_forall" "empty pending"
    | f :: fm =>
      (
      case f of 
        Ins(2,[v,body]) => expand_forall (v,body) instance br0 brm
      | _ => raise ERR "expand_branch_forall" "not a forall"
      )

fun drop_pending ({have, pending}: branch) =
  {have = have, pending = tl pending}

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val dropf_glob = ref (fn (_ : branch) => false) 

fun search br brm = 
  if null (#pending br) then false else 
  if (!dropf_glob) br then search (drop_pending br) brm else
  (
  case expand_branch br brm of
      [] => true (* no branch: unsatisfiable *)
    | newbr :: newbrm => search newbr newbrm (* at least one branch *)
  )
  
fun prove (premises : prog list) (phi : prog) : bool =
  let 
    val start : branch = {have = eempty prog_compare, pending = []}
    val initial_formulas = rev ((neg phi) :: premises)
    val _ = fresh_var_id := list_imin (List.concat (map all_varid initial_formulas)) - 1
  in
    case insert_list initial_formulas start of
      NONE => true
    | SOME br => search br []
  end

fun refute premises =
  let 
    val start : branch = {have = eempty prog_compare, pending = []}
    val _ = fresh_var_id := list_imin (List.concat (map all_varid premises)) - 1
  in
    case insert_list premises start of
      NONE => true
    | SOME br => search br []
  end

(* -------------------------------------------------------------------------
   Programming primitives
   ------------------------------------------------------------------------- *)

val timedv = Vector.fromList 
  [timed_hd, timed_tl, timed_push, 
   timed_is_var, timed_is_not, timed_is_or, timed_same_id,
   timed_cond, timed_while
  ]
   

(* -------------------------------------------------------------------------
   Example: Subsumption for R(3,3)
   ------------------------------------------------------------------------- *)
   
(*
load "qprove"; open qprove; open kernel aiLib;
val ERR = mk_HOL_ERR "test";

(* have the neural network learn subsumption 
   (maybe from the paper can a neural network learn entailment) 
 *)
 
term constructors: (make a proof to decide whether to drop? or something else)

binary operation take two states and return another state.

why can't + only one state (e.g. the two last states on the stack)?
and return a new state.

mp () ()

- either reach false or get to the theorem.


need access to have as a list and a set. 

 
fun subsumes have f = case f of
    Ins(0,[Ins(id,fl)]) => 
    (if id < 0 then emem f have else exists (subsumes have) fl)
  | Ins(id,fl) => 
    (if id < 0 then emem f have else exists (subsumes have) fl)
  
fun f ({have,pending}: branch) = subsumes have (hd pending);
dropf_glob := f;

fun v x = var (~x);
val taut1 = prove [] (or (v 1) (neg (v 1)));
val taut2 = prove [] (or (neg (v 1)) (v 2));
val taut3 = prove [] (neg (or (neg (v 1)) (neg (v 2))));

fun subsets_of_size 0 _ = [[]]
  | subsets_of_size _ [] = []
  | subsets_of_size n (x::xs) =
    let
      val with_x = map (fn ys => x::ys) (subsets_of_size (n-1) xs)
      val without_x = subsets_of_size n xs
    in
      with_x @ without_x
    end

val cliquel = subsets_of_size 3 (List.tabulate (6,I));

fun clique_of_subset_f f (subset,color) =
  let val edgel = all_pairs (dict_sort Int.compare subset) in
    map (fn x => (f x, color)) edgel
  end


fun ramsey_clauses_f f size (bluen,redn) = 
  let
    val bluesubsetl = subsets_of_size bluen (List.tabulate (size,I))
    val redsubsetl = subsets_of_size redn (List.tabulate (size,I))
    val subsetl = map_assoc (fn _ => 1) bluesubsetl @
                  map_assoc (fn _ => 2) redsubsetl
  in
    map (clique_of_subset_f f) subsetl
  end
  
fun ramsey_clauses_bare size (bluen,redn) = 
  ramsey_clauses_f I size (bluen,redn)
 
fun edge_to_var (x,y) = 
  if x < y then x + ((y * (y - 1)) div 2) else 
  raise ERR "edge_to_var" (its x ^ "-" ^ its y);
  
fun ramsey_clauses size (bluen,redn) =
  ramsey_clauses_f edge_to_var size (bluen,redn)



fun list_or l = case l of [] => raise ERR "" "" | [a] => a | a :: m =>
  or a (list_or m);

fun var_of_lit (a,b) = (if b=1 then neg else I) (var ((~a) - 1));
fun formula_of_clause clause = list_or (map var_of_lit clause);

val clauses = ramsey_clauses 6 (3,3);
val formulal = map formula_of_clause clauses;
val (b,t) = add_time refute formulal;
*)

(* -------------------------------------------------------------------------
   Language
   ------------------------------------------------------------------------- *)

(* 
primitives to decide whether to drop a clause or not: 
- subsumption (A true formula appears as positive formula in the clause)
- splitting on literals (only 2^15 maximum if do not speak on the same literal again)
- unit propagation
*)

 (*
 f state -> integer
 split > 0, drop = 0, soft drop < 0
 
 1) (5/6) destructor constructor (should i be able to construct my own terms)
    neg var or forall dest_ins_fst (dest_ins_snd (returns a list))
 
 2) mem list (made faster by looking up into the set)
 
 3) should be able to access the list of true formula in the branch 
 splits instead of just being a set. 
 4) should be able to have fast membership for that set.
 5) unit propagation/modus ponens 
    (do not really work in non-clausal form but eventually the thing would be clausal)
 6) is_literal
 7) cut (by a or not a)
 8) prove primitive 
 
 *)
 
 
 

end (* struct *)
