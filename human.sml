structure human :> human =
struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "human"

type prog = kernel.prog

val python_flag = ref false

fun mk_xn vn = if vn = ~1 then "x" else "X"
fun mk_yn vn = if vn = ~1 then "y" else "Y"
fun mk_zn vn = if vn = ~1 then "z" else "Z"

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
    fun f an =  
      if depend_on_z prog 
        then fs ^ "(" ^ mk_xn an ^ "," ^ mk_yn an ^ "," ^ mk_zn an ^ ")"
      else if depend_on_y prog 
        then fs ^ "(" ^ mk_xn an ^ "," ^ mk_yn an ^ ")"
      else fs ^ "(" ^ mk_xn an ^ ")"
      val fprev1 = f wn
      val fprev2 = f vn
      val fs_head = "def " ^ fprev1 ^ ":"
   in
     (fs_head, fprev2)
   end

fun get_vl p = 
  (if depend_on_x p then ["x"] else []) @
  (if depend_on_y p then ["y"] else []) @
  (if depend_on_z p then ["z"] else [])

fun human vn prog = 
  let 
    fun rhuman a p = rm_par (human a p)
    fun h p = human vn p
    fun rh p = rm_par (human vn p)
    fun hx p = human (~1) p
    fun rhx b = rm_par (human (~1) b)
    fun lrhx b = 
      let val vl = get_vl b in 
        "\\(" ^ String.concatWith "," vl ^ ")." ^  rhx b
      end
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
        ["  x = " ^ s3] @
        (if depend_on_z p1 then ["  z = x"]  else []) @
        ["  for y in range (1," ^ s2 ^ "):",
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
        ["  x,i = 0,0"] @
        (if depend_on_y p1 then ["  y = 0"]  else []) @
        (if depend_on_z p1 then ["  z = 0"]  else []) @
        ["  while i <= " ^ s2 ^ ":",
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
         "  for z in range (1," ^ s3 ^ "):",
         "    x,y = " ^ s1 ^ ", " ^ s2,
         "  return x"]
      end
    in
      wrap_def f
    end
  | Ins (14,[]) => mk_zn vn
  | Ins (15,[p1,p2,p3,p4,p5,p6,p7]) => 
    if not (!python_flag) 
      then "loop3(" ^ String.concatWith ", "
            [lrhx p1, lrhx p2, lrhx p3, rhx p4, rhx p5, rhx p6, rhx p7] ^ ")"
    else let fun f wn =
      let
        val (s1,s2,s3) = (hx p1, hx p2, hx p3)
        val s4 = human wn p4 ^ " + 1"
        val (s5,s6,s7) = (rhuman wn p5, rhuman wn p6, rhuman wn p7) 
      in
        ["  x,y,z = "  ^ s5 ^ ", " ^ s6 ^ ", " ^ s7,
         "  for i in range (1," ^ s4 ^ "):",
         "    x,y,z = " ^ s1 ^ ", " ^ s2 ^ ", " ^ s3,
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
    val s = human (~1) p
  in rm_par s end

fun human_python ntop p =
  let 
    val _ = python_flag := true
    val _ = ctxt := [] 
    val _ = funn := 0
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

fun parse_prog_aux sexp = case sexp of
    Stoken token => Ins (string_to_int token, [])
  | Sexp (Stoken token :: m)  => 
    Ins (string_to_int token, map parse_prog_aux m)
  | _ => raise ERR "parse_human" ""

fun parse_prog s = parse_prog_aux (parse_sexp s)
  handle HOL_ERR _ => raise ERR "parse_human" s

(*
load "rl"; open aiLib kernel human rl;
val p = random_prog 20;
print_endline (humanf p ^ "\n"); 
print_endline (human_python 32 p) ;
val p = parse_human "( * 1 1)";
print_endline (sexpr p);
*)


(* -------------------------------------------------------------------------
   Export to SMTlib
   ------------------------------------------------------------------------- *)

val defl = ref []
fun smt prog = 
  let fun sbinop s (p1,p2) = "(" ^ s ^ " " ^ smt p1 ^ " " ^ smt p2 ^ ")" in
  case prog of
    Ins (0,[]) => "0" 
  | Ins (1,[]) => "1" 
  | Ins (2,[]) => "2" 
  | Ins (3,[p1,p2]) => sbinop "+" (p1,p2)
  | Ins (4,[p1,p2]) => sbinop "-" (p1,p2) 
  | Ins (5,[p1,p2]) => sbinop "*" (p1,p2)
  | Ins (6,[p1,p2]) => sbinop "div" (p1,p2)
  | Ins (7,[p1,p2]) => sbinop "mod" (p1,p2)
  | Ins (8,[p1,p2,p3]) => 
    "(if " ^ smt p1 ^ " <= 0 then " ^ smt p2  ^ " else " ^ smt p3 ^ ")"
  | Ins (9,[p1,p2,p3]) =>
     if depend_on_x p3 orelse depend_on_y p3 orelse
        depend_on_y p2 orelse depend_on_y p1
     then raise ERR "smt" "not supported" 
     else 
       let val (r1,r2) = (smtdef "f1" p1, smtdef "f2" p2) in
         defl := !defl @ 
         ["f(0) = " ^ smt p3,
          "f(n+1) = (f1(f(n))",
          "g(x) = f(f2(x))"];
         "g(x)"
       end
  | Ins (10,[]) => "x"
  | Ins (11,[]) => raise ERR "smt" "not supported"
  | Ins (12,[p1,p2]) => raise ERR "smt" "not supported"
  | Ins (13,[p1,p2,p3,p4,p5]) => raise ERR "smt" "not supported"
  | _ => raise ERR "smt" (humanf prog)
  end
  
and smtdef s p = 
  let val r = smt p in
    defl := !defl @ [if depend_on_x p then "forall x." else "" 
      ^ s ^ "(x) = " ^ r]
  end


fun smttop s p = 
  let val _ = (defl := []; smtdef s p) in
    String.concatWith "\n" (!defl)
  end 

(* 
load "human"; open aiLib human;
val sl = readl "full-data5/sexpr_full";
val sl2 = map quadruple_of_list (mk_batch 4 sl);
val sl3 = map (fn (a,b,c,d) => (a,b, parse_prog c, parse_prog d)) sl2;
val p = #3 (hd sl3);
smttop "h" p;
val p2 = #4 (hd sl3);
print_endline (smttop "h2" p2);


*)









end (* struct *)
