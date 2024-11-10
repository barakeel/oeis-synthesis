(* ========================================================================= *)
(* DESCRIPTION   : Convert between strings and S-expressions                 *)
(* ========================================================================= *)

structure sexp :> sexp =
struct

val ERR = mk_HOL_ERR "sexp"

datatype sexp = Atom of string | Sexp of sexp list

fun push_buf buf acc = case buf of 
    [] => acc
  | _ => (implode (rev buf)) :: acc

fun lex_sexp_aux [] acc buf = rev (push_buf buf acc)
  | lex_sexp_aux (a :: m) acc buf =
      if Char.isSpace a then
        lex_sexp_aux m (push_buf buf acc) []
      else if mem a [#"(",#")"] then
        lex_sexp_aux m (String.str a :: push_buf buf acc) []
      else
        lex_sexp_aux m acc (a :: buf) 

fun lex_sexp str = lex_sexp_aux (explode str) [] []

fun parse_sexp acc l = case l of
    [] => raise ERR "parse_sexp" "unexpected"
  | "(" :: m => parse_sexp ([] :: acc) m
  | ")" :: m => 
    (
    case acc of 
      [] => raise ERR "parse_sexp" "closing parentheses"
    | [l] => Sexp (rev l) (* ignore remaining tokens *)
    | l1 :: l2 :: lm => parse_sexp ((Sexp (rev l1) :: l2) :: lm) m
    )
  | tok :: m => 
    (
    case acc of 
      [] => raise ERR "parseSexp" "missing open parentheses"
    | l :: lm => parse_sexp ((Atom tok :: l) :: lm) m
    )
     
fun string_to_sexp s = parse_sexp [] (lex_sexp s)

fun sexp_to_string sexp = case sexp of
    Atom s => s
  | Sexp sl => "(" ^ String.concatWith " " (map sexp_to_string sl) ^ ")"



end (* struct *)





