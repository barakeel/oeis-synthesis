structure hadamard :> hadamard =
struct

open HolKernel Abbrev boolLib aiLib
val ERR = mk_HOL_ERR "hadamard"

(* -------------------------------------------------------------------------
   Give a hadamard score to a function
   ------------------------------------------------------------------------- *)

fun self_scalar v offset =
  let
    val n = Vector.length v
    val sum = ref 0
    fun loop x = if x >= n then !sum else 
      (sum := !sum + Vector.sub (v,x) * Vector.sub (v,(x - offset) mod n);
       loop (x+1))  
  in
    loop 0
  end

fun wilson_score (v1,v2,v3,v4) = 
  let
    val n = Vector.length v1
    fun test offset = 
      self_scalar v1 offset + self_scalar v2 offset + 
      self_scalar v3 offset + self_scalar v4 offset = 0
    val scorel = map (fn x => if test x then 1 else 0) 
      (List.tabulate (n - 1, fn i => i + 1))
  in
    sum_int scorel
  end
  
fun wilson_score2 (v1,v2,v3,v4) = 
  let
    val score = ref 0
    val n = Vector.length v1
    fun test offset = score := !score + 
      Int.abs (self_scalar v1 offset + self_scalar v2 offset + 
               self_scalar v3 offset + self_scalar v4 offset)
    val _ = app test (List.tabulate (n - 1, fn i => i + 1))
  in
    !score
  end  
   
fun wilson_score3 (v1,v2,v3,v4) = 
  let
    val score = ref 0
    val n = Vector.length v1
    fun test offset = 
      if offset >= n then () else
      let val r = self_scalar v1 offset + self_scalar v2 offset + 
                  self_scalar v3 offset + self_scalar v4 offset
      in
        if r = 0 then (incr score; test (offset + 1)) else ()
      end
    val _ = test 1
  in
    ~ ((!score * 10000) div (n-1))
  end
   
(* -------------------------------------------------------------------------
   Basic MCTS
   ------------------------------------------------------------------------- *)
   
val movel1 = [[~1,~1,~1,1],[~1,~1,1,~1],[~1,1,~1,~1],[1,~1,~1,~1]]
val movel2 = map (map (fn x => ~1 * x)) movel1;
val movel = movel1 @ movel2
val movev = Vector.fromList (movel1 @ movel2);
fun random_move () = let val n = random_int (0,7) in Vector.sub (movev,n) end
   
exception Success of int list list;

val size_glob = ref 17

fun simul state =
  let 
    val r = ref 0
    val staten = length state
    val _ = if staten > !size_glob then raise ERR "simul" (its staten) else ()
    val finalstate = state @
       List.tabulate (!size_glob - staten, fn _ => random_move ())
    val l = list_combine finalstate
    val vq = quadruple_of_list (map Vector.fromList l)
    val sc = wilson_score2 vq
  in
    if sc = 0 then raise Success l else 1.0 - int_div sc 
      ((!size_glob - 1) * 4 * !size_glob)
  end


fun ilts il = String.concatWith " " (map its il); 


(* -------------------------------------------------------------------------
   Real MCTS
   -------------------------------------------------------------------------
*)   

val explo = ref 1.0

val moven = length movel

type move = int list
datatype mtree = MNode of 
  move list * real ref * real ref  * mtree option ref vector 

val parentref = ref []

fun empty_cv () = Vector.tabulate (moven, fn _ => ref NONE)

val orgstate = [[1,1,1,1]]   
fun init_tree () = MNode (orgstate, ref (simul orgstate), ref 1.0, empty_cv ())

fun ucb vispar co = case (!co) of 
    NONE => 1000000.0 + random_real ()
  | SOME (MNode (_,sum,vis,_)) => 
      !sum / !vis + !explo * (Math.sqrt vispar / !vis)
      
      (* Math.sqrt (Math.ln vispar / !vis)) *)

fun select (mtree as (MNode (_,sum,vis,cv))) =
  let 
    val _ = parentref := (sum,vis) :: !parentref
    val ci = vector_maxi (ucb (!vis)) cv
  in
    case !(Vector.sub (cv,ci)) of 
      NONE => (mtree,ci)
    | SOME newmtree => select newmtree
  end
  
fun update_cv state cv sc ci =
  let val r = Vector.sub (cv,ci) in 
    r := SOME 
     (MNode (state , ref sc, ref 1.0, empty_cv ()))
  end
    
fun update_parent sc (sum,vis) = (sum := !sum + sc; vis := !vis + 1.0)
    
fun expand (mtree as MNode (state,sum,vis,cv), ci) = 
  if length state >= !size_glob then
    app (update_parent (!sum / !vis)) (!parentref)
  else
  let 
    val newstate = state @ [Vector.sub (movev,ci)]
    val sc = simul newstate  
  in
    update_cv newstate cv sc ci;
    app (update_parent sc) (!parentref) 
  end

fun mcts_once mtree =
  let 
    val _ = parentref := []
    val (mnode,ci) = select mtree 
  in 
    expand (mnode,ci)
  end
   
fun mcts mtree nsim = 
  if nsim <= 0 
  then mtree 
  else (mcts_once mtree; mcts mtree (nsim - 1))  
   
   
end (* struct *)


(*
load "hadamard"; open hadamard;
PolyML.print_depth 5;
open aiLib;

fun ilts il = String.concatWith " " (map (fn x => if x = 1 then "1" else "0") il);

fun vis_of co = case (!co) of 
    NONE => 0.0
  | SOME (MNode (_,sum,vis,_)) => !vis;

fun select_maxvis mtree = case mtree of MNode (_,r1,r2,cv) => 
  let val ci = vector_maxi vis_of cv in
    print_endline (pretty_real (!r1 / !r2) ^ ": " ^ ilts (Vector.sub (movev,ci)));
    valOf (!(Vector.sub (cv,ci)))
  end;
 

fun loop nsim mtree = case mtree of MNode (state,_,_,_) => 
  if length state = !size_glob then print_endline "failure" else
  (loop nsim (select_maxvis (mcts mtree nsim)));

size_glob := 5;
explo := 1.0;
app (fn () => loop 10000 (init_tree ())) (List.tabulate (100, fn _ => ()));

  

  
  
  
  
  

*)
