(* ========================================================================= *)
(* DESCRIPTION   : Syntax of Qprover                                         *)
(* ========================================================================= *)

structure qsyntax :> qsyntax = struct

open HolKernel Abbrev boolLib aiLib kernel sexp
val ERR = mk_HOL_ERR "qsyntax"
type formula = kernel.prog

(* -------------------------------------------------------------------------
   Syntax
   ------------------------------------------------------------------------- *) 

val not_id = 0
val or_id = 1
val forall_id = 2
val eq_id = 3
val zero_id = 4
val suc_id = 5
val add_id = 6

fun is_eq (Ins(id,_)) = id = eq_id
fun is_neg (Ins(id,_)) = id = not_id
fun is_varid id = id < 0
fun neg f = case f of Ins (0,[g]) => g | _ => Ins (0,[f])

(* -------------------------------------------------------------------------
   Human interface
   ------------------------------------------------------------------------- *) 

val humanv = Vector.fromList ["not","or","forall","=","0","suc","+"]
val arityv = Vector.fromList [1,2,2,2,0,1,2]
val humand = dnew String.compare (number_snd 0 (vector_to_list humanv));

fun id_of_oper s = 
  if hd_string s = #"x" 
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
  | Sexp (Atom s :: argl) => 
    let val n = id_of_oper s in 
      if length argl <> Vector.sub (arityv, n) 
      then raise ERR "sexp_to_formula" ("arity: " ^ s) 
      else Ins (n, map sexp_to_formula argl)
    end 
  | _ => raise ERR "sexp_to_formula" "";

fun human_of_formula (Ins (i,pl)) = 
  let val opers = 
    if i < 0 then "x" ^ its (~i) else
    if i >= Vector.length humanv then "f" ^ its i else 
    Vector.sub (humanv,i) 
  in
    if null pl then opers else
    "(" ^ String.concatWith " " (opers :: map human_of_formula pl) ^ ")"
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
   Timers
   ------------------------------------------------------------------------- *)

fun checktimern n = 
  (
  abstimer := !abstimer + n; 
  if !abstimer > !timelimit then raise ProgTimeout else ()
  )

fun checktimer () = checktimern 1

fun timed_formula_compare (Ins x,Ins y) =
  (
  incr abstimer;
  cpl_compare Int.compare (list_compare timed_formula_compare) (x,y)
  )
 
  
end
