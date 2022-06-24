structure human :> human =
struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "human"

type prog = kernel.prog

val python_flag = ref false

fun mk_xn vn = if vn = ~1 then "x" else "X"
fun mk_yn vn = if vn = ~1 then "y" else "Y"

fun rm_par s = 
  if String.size s = 0 then s else
  if String.sub (s,0) = #"(" andalso String.sub (s,String.size s - 1) =  #")" 
  then String.substring (s,1,String.size s - 2)
  else s;

(* -------------------------------------------------------------------------
   Printing to custom language or Python 
   ------------------------------------------------------------------------- *)

fun is_loop (Ins(id,pl)) = mem id [9,12,13,16]

val ctxt = ref []
val funn = ref 0
fun incrs s = s ^ " = " ^ s ^ " + 1";
fun decrs s = s ^ " = " ^ s ^ " - 1";

fun mk_def vn wn prog =
  let
    val fs = "f" ^ its wn
      val fprev1 = if depend_on_y prog 
        then fs ^ "(" ^ mk_xn wn ^ "," ^ mk_yn wn ^ ")"
        else fs ^ "(" ^ mk_xn wn ^ ")"
      val fprev2 = if depend_on_y prog 
        then fs ^ "(" ^ mk_xn vn ^ "," ^ mk_yn vn ^ ")"
        else fs ^ "(" ^ mk_xn vn ^ ")"
      val fs_head = "def " ^ fprev1 ^ ":"
   in
     (fs_head, fprev2)
   end

fun human vn prog = 
  let 
    fun rhuman a p = rm_par (human a p)
    fun h p = human vn p
    fun rh p = rm_par (human vn p)
    fun hx p = human (~1) p
    fun rhx b = rm_par (human (~1) b)
    fun lrhx b = "\\(x,y)." ^ rhx b
    fun sbinop s (p1,p2) = "(" ^ h p1 ^ " " ^ s ^ " " ^ h p2 ^ ")"  
    fun sunop s p1 = s ^ "(" ^ rh p1 ^ ")"
    fun wrap_def f =
      let
        val wn = (!funn)
        val _ = incr funn
        val (fs_head, fprev2) = mk_def vn wn prog
        val cs = fs_head :: f wn @ [""]
      in
        ctxt := !ctxt @ cs; fprev2
      end
  in
  case prog of
    Ins (3,[p1,p2]) => sbinop "+" (p1,p2)
  | Ins (4,[p1,p2]) => sbinop "-" (p1,p2) 
  | Ins (5,[p1,p2]) => sbinop "*" (p1,p2)
  | Ins (6,[p1,p2]) => sbinop (if !python_flag then  "//" else "div") (p1,p2)
  | Ins (7,[p1,p2]) => sbinop (if !python_flag then  "%" else "mod") (p1,p2)
  | Ins (8,[p1,p2,p3]) => 
    if !python_flag
    then "(" ^ h p2 ^ " if " ^ h p1 ^ " <= 0 else " ^ h p3 ^ ")"
    else "(if " ^ h p1 ^ " <= 0 then " ^ h p2  ^ " else " ^ h p3 ^ ")"
  | Ins (9,[p1,p2,p3]) => 
    if not (!python_flag) then
      "loop(" ^ String.concatWith ", " [lrhx p1, rhx p2, rhx p3] ^ ")"
    else let fun f wn =
      let val (s1,s2,s3) = (rhx p1, human wn p2 ^ " + 1", rhuman wn p3) in
        ["  x = " ^ s3,
         "  for y in range (1," ^ s2 ^ "):",
         "    x = " ^ s1,
         "  return x"]
      end
    in
      wrap_def f
    end
  | Ins (10,[]) => mk_xn vn
  | Ins (11,[]) => mk_yn vn
  | Ins (12,[p1,p2]) => 
    if not (!python_flag) then "compr(" ^ lrhx p1 ^ ", " ^ rhx p2 ^ ")" else 
    let fun f wn = 
      let val (s1,s2) = (hx p1, rhuman wn p2) in
        ["  x,y,i = 0,0,0",
         "  while i <= " ^ s2 ^ ":",
         "    if " ^ s1 ^ " <= 0:",
         "      i = i + 1",
         "    x = x + 1",
         "  return x - 1"]
      end
    in
      wrap_def f
    end
  | Ins (13,[p1,p2,p3,p4,p5]) => 
    if not (!python_flag) 
      then "loop2(" ^ String.concatWith ", "
            [lrhx p1, lrhx p2, rhx p3, rhx p4, rhx p5] ^ ")"
    else let fun f wn =
      let
        val (s1,s2) = (hx p1, hx p2)
        val s3 = human wn p3 ^ " + 1"
        val (s4,s5) = (rhuman wn p4, rhuman wn p5) 
      in
        ["  x,y = "  ^ s4 ^ ", " ^ s5,
         "  for i in range (1," ^ s3 ^ "):",
         "    x,y = " ^ s1 ^ ", " ^ s2,
         "  return x"]
      end
    in
      wrap_def f
    end
  | Ins (s,[]) => its s
  | Ins (s,l) => "(" ^ its s ^ " " ^ String.concatWith " " (map h l) ^ ")"
  end

fun humanf p =
  let 
    val _ = python_flag := false
    val s = human (~1) (undef_prog p)
  in rm_par s end

fun human_python ntop ptop =
  let 
    val _ = python_flag := true
    val _ = ctxt := [] 
    val _ = funn := 0
    val p = undef_prog ptop
    val ps = 
      if not (is_loop p) then
      let
        val wn = !funn
        val _ = incr funn
        val fs = "f" ^ its wn
        val xs = mk_xn wn
        val s = rm_par (human wn p)
        val head = "def " ^ fs ^ "(" ^ xs ^ "):\n  return " ^ s ^ "\n"
        val test = "for x in range(" ^ its ntop ^ 
          "):\n  print (" ^ fs ^ "(x))"    
        val ps' = String.concatWith "\n" (!ctxt @ [head,test])
      in ps' end
      else
      let
        val wn = !funn
        val fs = "f" ^ its wn
        val s = rm_par (human wn p)
        val test = "for x in range(" ^ its ntop ^ 
          "):\n  print (" ^ fs ^ "(x))"    
        val ps' = String.concatWith "\n" (!ctxt @ [test])
      in ps' end
    val _ = ctxt := [] 
    val _ = python_flag := false
  in
    ps
  end

(* -------------------------------------------------------------------------
   S-expressions I/O
   ------------------------------------------------------------------------- *)

datatype sexp = Sexp of sexp list | Stoken of string

fun lex_sexp_aux buf sl charl = case charl of
    [] => if null buf then rev sl else rev (implode (rev buf) :: sl)
  | #"(" :: m => 
   (
   if null buf 
   then lex_sexp_aux [] ("(" :: sl) m
   else lex_sexp_aux [] ("(" :: implode (rev buf) :: sl) m
   )
  | #")" :: m => 
   (
   if null buf 
   then lex_sexp_aux [] (")" :: sl) m
   else lex_sexp_aux [] (")" :: implode (rev buf) :: sl) m
   )
  | #" " :: m => 
   (
   if null buf 
   then lex_sexp_aux [] sl m
   else lex_sexp_aux [] (implode (rev buf) :: sl) m
   )
  | a :: m => lex_sexp_aux (a :: buf) sl m
  
fun lex_sexp s = lex_sexp_aux [] [] (explode s)
 
fun parse_sexpl sexpl sl = case sl of
    [] => (rev sexpl, [])
  | "(" :: m =>
    let val (a,contl) = parse_sexpl [] m in
      parse_sexpl (Sexp a :: sexpl) contl     
    end
  | ")" :: m => (rev sexpl, m)
  | a :: m => parse_sexpl (Stoken a :: sexpl) m 

fun parse_sexp s =
  let val (l1,l2) = parse_sexpl [] (lex_sexp s) in
    case (l1,l2) of
     ([a],[]) => a 
    | _ => raise ERR "parse_sexp" s
  end

val tokenl =    
  ["0","1","2","+","-","*","/","%","cond","loop","x","y","compr","loop2"]
val tokend = dnew String.compare (number_snd 0 tokenl)
val tokenv = Vector.fromList tokenl

fun parse_human_aux sexp = case sexp of
    Stoken token => Ins (dfind token tokend, [])
  | Sexp (Stoken token :: m)  => 
    Ins (dfind token tokend, map parse_human_aux m)
  | _ => raise ERR "parse_human" ""
  
fun parse_human s = parse_human_aux (parse_sexp s)
  handle HOL_ERR _ => raise ERR "parse_human" s
 
fun sexpr (Ins (id,pl)) =
  if null pl then its id else 
  "(" ^ String.concatWith " " (Vector.sub (tokenv,id) :: map sexpr pl) ^ ")";  

(*
load "rl"; open aiLib kernel human rl;
val p = random_prog 20;
print_endline (humanf p ^ "\n"); 
print_endline (human_python 32 p) ;
val p = parse_human "( * 1 1)";
print_endline (sexpr p);
*)

end (* struct *)
