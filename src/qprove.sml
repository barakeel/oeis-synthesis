(* ========================================================================= *)
(* DESCRIPTION   : Theorem prover                                            *)
(* ========================================================================= *)

structure qprove :> qprove = struct

open HolKernel Abbrev boolLib aiLib kernel
val ERR = mk_HOL_ERR "qprove"

type prog = kernel.prog
type formula = kernel.prog
type qprove = (formula list * (prog * int))
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

fun list_hd a = case a of e :: m => [e] | _ => raise Error 
fun list_tl a = case a of e :: m => m | _ => raise Error 
fun list_push a b = case a of e :: m => e :: b | _ => raise Error
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
fun is_v (Ins(i,_)) = i < 0
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

val timed_is_v = timed_unary (test_wrap is_v)
val timed_is_not = timed_unary (test_wrap is_not)
val timed_is_or = timed_unary (test_wrap is_or)
val timed_same_id = timed_binary same_id

fun dest x = case x of 
    Ins(_,l) :: m => l @ m
  | _ => raise Error 

val timed_dest = timed_unary dest

(* -------------------------------------------------------------------------
   Branch insertion: add a new fact to the branch
   ------------------------------------------------------------------------- *)

type branch = {have : prog Redblackset.set, 
               havel : prog list, 
               pending : prog list}

fun timed_emem p d = 
  (abstimer := (!abstimer) + 
     IntInf.log2 (1 + IntInf.fromInt (elength d)) + prog_size p;
   emem p d)

fun insert f (br as {have, havel, pending}) =
  if timed_emem (neg f) have then NONE else
  if timed_emem f have then SOME br else
    SOME {have = eadd f have, 
          havel = f :: havel,
          pending = if non_lit f then f :: pending else pending}

(* not sure if this if non_lit apply to first-order *)

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

fun expand_branch ({have, havel, pending}: branch) (brm: branch list) = case pending of
      [] => raise ERR "expand_branch" "empty pending"
    | f :: fm =>
      let val br0 = {have = have, havel = havel, pending = fm} in
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

fun drop_pending ({have, havel, pending}: branch) =
  {have = have, havel = havel, pending = tl pending}

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val dropf_glob = ref (fn (_ : branch) => false) 

fun search br brm = 
  (
  abstimer := (!abstimer) + 5;
  if null (#pending br) then false else 
  if (!dropf_glob) br then search (drop_pending br) brm else
  (
  case expand_branch br brm of
      [] => true (* no branch: unsatisfiable *)
    | newbr :: newbrm => search newbr newbrm (* at least one branch *)
  )
  )
  
fun prove (premises : prog list) (phi : prog) : bool =
  let 
    val start : branch = {have = eempty prog_compare, havel = [], pending = []}
    val initial_formulas = rev ((neg phi) :: premises)
    val _ = fresh_var_id := list_imin (List.concat (map all_varid initial_formulas)) - 1
  in
    case insert_list initial_formulas start of
      NONE => true
    | SOME br => search br []
  end

fun refute premises =
  let 
    val start : branch = {have = eempty prog_compare, havel = [], pending = []}
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
    fun f br = null (exec (#pending br, #havel br))
    val _ = dropf_glob := f 
    val b = 
      let val b' = prove [] phi in
        if b' then incr unsat_count else incr sat_count; b'
      end
      handle Error => (incr error_count; false) 
           | ProgTimeout => (incr timeout_count; false)
  in 
    (b,!abstimer)
  end

fun qprove_baseline phi = 
  let 
    val _ = abstimer := 0
    val _ = dropf_glob := (fn (_ : branch) => false)
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
   Input output and benchmark
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

fun human_formula (Ins (i,pl)) = 
  if i < 0 then ("v" ^ its (~i)) else 
  let val opers = 
    if i = 0 then "not" else if i = 1 then "or" else "f" ^ its i
  in
    "(" ^ String.concatWith " " (opers :: map human_formula pl) ^ ")"
  end
    
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


(*
fun v x = var (~x);
val taut1 = prove [] (or (v 1) (neg (v 1)));
val taut2 = prove [] (or (neg (v 1)) (v 2));
val taut3 = prove [] (neg (or (neg (v 1)) (neg (v 2))));  
*)

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
   Example: SAT solving
   ------------------------------------------------------------------------- *)
   
(*
load "qprove"; open qprove; open kernel aiLib;
val ERR = mk_HOL_ERR "test";


val timd = dnew prog_compare formulaltim;

load "search";
search.randsearch_flag := true;
checkinit_qprove ();
search.search (0,20.0);
PolyML.print_depth 2;
val rl = checkfinal_qprove ();
PolyML.print_depth 40;

fun f (formulal,(p,sc)) = 
  let val oldsc = sum_int (map (fn x => dfind x timd) formulal) in
    if oldsc < sc then 0 else oldsc - sc 
  end;

fun g (formulal,(p,sc)) = 
  let val oldsc = sum_int (map (fn x => dfind x timd) formulal) in
    oldsc
  end;

int_div (sum_int (map f rl)) (length rl);
int_div (sum_int (map g rl)) (length rl);



load "game";
checkinit_qprove ();
fun f () = checkonline_qprove (game.random_prog 40);
fun calln n f = if n < 0 then () else (f (); calln (n-1) f);
val (_,t) = add_time (calln 100000) f;


    val phil = random_elem formulal8
    val rl = map_assoc (qprove p) phil;
    map snd rl;
    



load "qprove"; load "game"; load "human"; 
open qprove; open kernel aiLib;
val ERR = mk_HOL_ERR "test";

val dir = "/home/thibault/logical-entailment-dataset/data";
val filel = listDir dir;
val orgl = read_true_exl (dir ^ "/test_easy.txt");
val easyl8 = readl_string_of
val dhol = dnew prog_compare (combine (easyl,orgl));





val p = hd easyl8';
val p'= prog_of_string (string_of_prog p);



(* 
run the search for a long time (easy to parallelize since the
formula set are picked at random). run with notarget_flag and
*)



val directl = map f easyl;
val directl1 = filter (fst o snd) directl;
fun g (p,(b,tim)) = (p,tim);
val directl2 = dict_sort (fst_compare prog_compare_size) directl1; 

val d = ref (dempty prog_compare)




d := dempty prog_compare;  
val (_,t) = add_time (calln 1000000) f;
dlength (!d);

val inventl = dict_sort (fst_compare prog_compare_size) (dlist (!d));

val l1 = combine (directl2,inventl);
fun f ((phi1,(b1,tim1)),(phi2,(p2,tim2))) = 
  if prog_compare (phi1,phi2) = EQUAL andalso b1 then
    ((phi1,p2),tim1-tim2)
  else raise ERR "f" "" 

val l2 = dict_sort compare_imax (map f l1);
val (l3,l4) = partition (fn x => snd x < 0) l2; length l3; length l4;

fun f ((phi1,(b1,tim1)),(phi2,(p2,tim2))) = 
  if prog_compare (phi1,phi2) = EQUAL andalso b1 then
    ((phi1,p2),int_div tim1 tim2)
  else raise ERR "f" "" 

val l2 = dict_sort compare_rmax (map f l1);
val ((phi,p),r) = hd l2;

print_endline (human.human_trivial p);
print_endline (term_to_string (dfind phi dhol));

*)

(* -------------------------------------------------------------------------
   Example: Subsumption for R(3,3)
   ------------------------------------------------------------------------- *)

(*
fun subsumes have f = case f of
    Ins(0,[Ins(id,fl)]) => 
    (if id < 0 then emem f have else exists (subsumes have) fl)
  | Ins(id,fl) => 
    (if id < 0 then emem f have else exists (subsumes have) fl)
  
fun f ({have,pending}: branch) = subsumes have (hd pending);
dropf_glob := f;

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

 
 
 

end (* struct *)
