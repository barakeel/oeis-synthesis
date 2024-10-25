structure human :> human =
struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "human"

type prog = kernel.prog


val use_list = ref false

fun rm_par s = (* if !use_list then s else *)
  if String.size s = 0 then s else
  if String.sub (s,0) = #"(" andalso String.sub (s,String.size s - 1) =  #")" 
  then String.substring (s,1,String.size s - 2)
  else s;


fun mk_xn vn = if vn = ~1 then "x" else "X"
fun mk_yn vn = if vn = ~1 then "y" else "Y"
fun mk_zn vn = if vn = ~1 then "z" else "Z"
fun is_loop (Ins(id,pl)) = mem id [9,12,13,16]
val ctxt = ref []
val funn = ref 0


(* -------------------------------------------------------------------------
   Push and pop operations 
   ------------------------------------------------------------------------- *)

fun aconst s = if !use_list then "S(" ^ s ^ ")" else s
fun dothead s = if !use_list then "H(" ^ s ^ ")" else s
fun dotpop s = "pop(" ^ s ^ ")"
fun dotpush s1 s2 = "push(" ^ s1 ^ "," ^ s2 ^ ")"

(* -------------------------------------------------------------------------
   Printing to Python 
   ------------------------------------------------------------------------- *)

fun incrs s = s ^ " = " ^ s ^ " + 1";
fun decrs s = s ^ " = " ^ s ^ " - 1";

fun mk_def vn wn prog =
  let
    val fs = "f" ^ its wn
    val fsperm = if !fs_flag then fs ^ "(perm," else fs ^ "("
    fun f an = fsperm ^  
      (if depend_on_z prog 
        then mk_xn an ^ "," ^ mk_yn an ^ "," ^ mk_zn an ^ ")"
      else if depend_on_y prog 
        then mk_xn an ^ "," ^ mk_yn an ^ ")"
      else mk_xn an ^ ")"
      )
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
    Ins (0,[]) => aconst (its 0)
  | Ins (1,[]) => aconst (its 1)
  | Ins (2,[]) => aconst (its 2)
  | Ins (3,[p1,p2]) => sbinop "+" (p1,p2)
  | Ins (4,[p1,p2]) => sbinop "-" (p1,p2) 
  | Ins (5,[p1,p2]) => sbinop "*" (p1,p2)
  | Ins (6,[p1,p2]) => sbinop "//" (p1,p2)
  | Ins (7,[p1,p2]) => sbinop "%" (p1,p2)
  | Ins (8,[p1,p2,p3]) => 
    "(" ^ h p2 ^ " if " ^ dothead (h p1) ^ " <= 0 else " ^ h p3 ^ ")"
  | Ins (9,[p1,p2,p3]) => 
    let fun f wn =
      let val (s1,s2,s3) = (rhx p1, dothead (human wn p2) ^ " + 1", 
        rhuman wn p3) 
      in
        ["  x = " ^ s3] @
        (if !use_list then ["  i = 1"] else []) @
        (if depend_on_z p1 then ["  z = x"]  else []) @
        (if !use_list
         then
         ["  while i < " ^ s2 ^ ":",
          "    y = " ^ aconst "i",
          "    i = i + 1",
          "    x = " ^ s1,
          "  return x"]
         else
        ["  for y in range (1," ^ s2 ^ "):",
         "    x = " ^ s1,
         "  return x"])      
      end
    in
      wrap_def f
    end
  | Ins (10,[]) => mk_xn vn
  | Ins (11,[]) => mk_yn vn
  | Ins (12,[p1,p2]) =>
    let fun f wn = 
      let val (s1,s2) = (hx p1, dothead (rhuman wn p2)) in
        ["  x,i = " ^ aconst "0" ^ ",0"] @
        (if depend_on_y p1 then ["  y = " ^ aconst "0"]  else []) @
        (if depend_on_z p1 then ["  z = " ^ aconst "0"]  else []) @
        ["  while i <= max(" ^ s2 ^ ",0):",
         "    if " ^ dothead s1 ^ " <= 0:",
         "      i = i + 1",
         "    x = x + " ^ aconst "1",
         "  return x - " ^ aconst "1"]
      end
    in
      wrap_def f
    end
  | Ins (13,[p1,p2,p3,p4,p5]) => 
    let fun f wn =
      let
        val (s1,s2) = (hx p1, hx p2)
        val s3 = dothead (human wn p3) ^ " + 1"
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
    let fun f wn =
      let
        val (s1,s2,s3) = (hx p1, hx p2, hx p3)
        val s4 = dothead (human wn p4) ^ " + 1"
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
  | Ins (14,[p1,p2]) => dotpush (h p1) (h p2)
  | Ins (15,[p1]) => dotpop (h p1)
  | Ins (id,[]) => name_of_oper id
  | Ins (id,l) => 
    name_of_oper id ^ "(" ^ String.concatWith ", " (map rh l) ^ ")"
  end

(* Warning: 
   does not support programs that depend on y 
   does not support subprograms that 
     depends on z and contains push and pop
*)
val preambule = readl (selfdir ^ "/intl_preambule")
   
fun human_python ntop ptop =
  let
    val p = zeroy ptop
    val _ = use_list := 
      (contain_opers "pop" p orelse contain_opers "push" p)
    val _ = ctxt := [] 
    val _ = funn := 0
    val preamb = if !use_list then preambule @ [""] else []
    val ps = 
      if not (is_loop p) then
      let
        val wn = !funn
        val _ = incr funn
        val fs = "f" ^ its wn
        val fsperm = if !fs_flag then fs ^ "(perm," else fs ^ "("
        val xs = mk_xn wn
        val ys = mk_yn wn
        val s = rm_par (human wn p)
        val head = "def " ^ fsperm ^ xs ^ "):\n  return " ^ s ^ "\n"
        val prints = "print(" ^ dothead (fs ^ "(" ^ aconst "x" ^ ")") ^ ")"
        val test = 
          "for x in range(" ^ its ntop ^ "):\n  " ^ prints 
        val ps' = String.concatWith "\n" (preamb @ !ctxt @ [head] @ 
          (if !fs_flag then [] else [test]))
      in ps' end
      else
      let
        val wn = !funn
        val fs = "f" ^ its wn
        val s = rm_par (human wn p)
        val prints = 
          if !use_list 
          then "print(" ^ dothead (fs ^ "(" ^ aconst "x" ^ ")") ^ ")"
          else "print(" ^ fs ^ "(x))" 
        val test = 
          "for x in range(" ^ its ntop ^ "):\n  " ^ prints 
        val ps' = String.concatWith "\n" (preamb @ !ctxt @ 
          (if !fs_flag then [] else [test]))
      in ps' end
    val _ = ctxt := []
  in
    use_list := false;
    ps
  end

(* -------------------------------------------------------------------------
   Printing to custom language
   ------------------------------------------------------------------------- *)

fun human_trivial p = 
  let fun h p = human_trivial p in
    case p of
      Ins (id,[]) => name_of_oper id
    | Ins (id,pl) => 
      "(" ^ String.concatWith " "  (name_of_oper id :: map h pl) ^ ")"
  end

fun human_simple p = 
  let   
    fun h p = human_simple p
    fun sbinop s (p1,p2) = "(" ^ h p1 ^ " " ^ s ^ " " ^ h p2 ^ ")"  
  in
    case p of
      Ins (0,[]) => its 0
    | Ins (1,[]) => its 1
    | Ins (2,[]) => its 2
    | Ins (3,[p1,p2]) => sbinop "+" (p1,p2)
    | Ins (4,[p1,p2]) => sbinop "-" (p1,p2) 
    | Ins (5,[p1,p2]) => sbinop "*" (p1,p2)
    | Ins (6,[p1,p2]) => sbinop "div" (p1,p2)
    | Ins (7,[p1,p2]) => sbinop "mod" (p1,p2)
    | Ins (8,[p1,p2,p3]) => 
      "(if " ^ h p1 ^ " <= 0 then " ^ h p2  ^ " else " ^ h p3 ^ ")"
    | Ins (id,[]) => name_of_oper id
    | Ins (id,pl) => 
      "(" ^ String.concatWith " " (name_of_oper id :: map h pl) ^ ")"
  end

fun humanf p = 
  if !minimal_flag 
  then human_trivial p
  else human_simple p


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

exception Arity of int * int

fun apply_move move board =
  let 
    val arity = arity_of_oper move
    val (l1,l2) = part_n arity board 
  in
    if length l1 <> arity 
    then raise Arity (move,length l1)
    else Ins (move, rev l1) :: l2
  end

fun human_gpt s = 
  let 
    val ml = tokenl_of_gpt s
    val progl = foldl (uncurry apply_move) [] ml
  in
    print_endline (String.concatWith "\n\n" (map (human_python 32) progl))
  end
  handle Arity (i1,i2) => 
    print_endline (its i1 ^ "does not have arity" ^ its i2)


val fsmapnamel = [
("cactus evacuation",126),
("Lehmer code rotation",149),
("Demazure product with inverse",159),
("inverse Foata bijection",175),
("runsort",223),
("descent views to invisible inversion bottoms",235),
("Clarke-Steingrimsson-Zeng inverse",236),
("descent views to invisible inversion bottoms",237),
("Clarke-Steingrimsson-Zeng",238),
("Corteel",239),
("invert Laguerre heap",241),
("restriction",252),
("Inverse fireworks map",254),
("Alexandersson Kebede",257),
("conjugation by long cycle",265),
("catalanization",277),
("Backward Rotation",279),
("Lehmer-code to major-code bijection",62),
("reverse",64),
("inverse",66),
("Foata bijection",67),
("Simion-Schmidt map",68),
("complement",69),
("major-index to inversion-number bijection",73),
("first fundamental transformation",86),
("inverse first fundamental transformation",87),
("Kreweras complement",88),
("Inverse Kreweras complement",89),
("cycle-as-one-line notation",90)
];


val fsmapnamed = dnew Int.compare (map swap fsmapnamel);
fun find_fsname s = dfind (string_to_int (tl_string (tl_string s)))  
  fsmapnamed 
  handle NotFound => raise ERR "find_fsname" s

(*
load "rl"; open aiLib kernel human rl;
val p = game.random_prog 20;
print_endline (humanf p ^ "\n"); 
print_endline (human_python 32 p) ;
val s = gpt_of_prog p;
val p = parse_human "( * 1 1)";
print_endline (sexpr p);

human_gpt s;
*)

(*
load "human"; open aiLib kernel human;
val s = "K L O L P P P P P C G P E K D K K B E B B N P P P P P C G P";
human_gpt s;


*)

(* 
load "rl"; open aiLib kernel human rl bloom;

val itsol20 = read_itprogl "itsol20";
val fs3_itsol15 = read_itprogl "fs3_itsol15";
val abillion = 1000 * 1000 * 1000
fun string_of_tp (t,p) =
  "size " ^ its (prog_size p) ^ ", " ^
  (
  if t < abillion
  then ("correct all, time " ^ its t)
  else ("correct " ^ its (abillion + 10000 - t))
  ) 
  ^ ": " ^ humanf p ^ "\n\n" ^ human_python 10 p ^ "\n\n";
  
fun string_of_itprog (i,tpl) = 
  let 
    val out1 = valOf (Array.sub (oseq,i)) 
    val out2 = map (fn x => Vector.sub (permv,IntInf.toInt x)) out1
    val perminputl = vector_to_list perminputv
    val io = combine (perminputl,out2)
    val mapsl = rev (Vector.sub (compv,i))
    val mapslh = map find_fsname mapsl
    fun f (a,b) = 
      "[" ^ String.concatWith "," (map its a) ^ "]" ^ " -> " ^
      "[" ^ String.concatWith "," (map its b) ^ "]"
  in
    String.concatWith "o" mapsl ^ "\n" ^ 
    String.concatWith "  o  " mapslh ^ "\n" ^ 
    String.concatWith "\n" (map f io) ^ "\n" ^
    String.concatWith "\n" (map string_of_tp tpl)
  end

fun stats_sol itsol =
  let
    val itsolsort = dict_sort 
      (snd_compare (list_compare (snd_compare prog_compare_size))) itsol
  in
    writel "fs3_itsol15_human" (map string_of_itprog itsolsort)
  end;

stats_sol fs3_itsol15;

*)

end (* struct *)
