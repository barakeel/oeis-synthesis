structure human :> human =
struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "human"

type prog = kernel.prog

val polynorm_flag = ref false
val imperative_flag = ref false
val nolam_flag = ref false

fun mk_xn vn = if vn = ~1 then "x" else "X"
fun mk_yn vn = if vn = ~1 then "y" else "Y"

(* -------------------------------------------------------------------------
   Polynomial normalization 
   (todo: message users to turn it off when it fails)
   ------------------------------------------------------------------------- *)

fun itsm i = if i < 0 then "-" ^ its (~i) else its i

fun polyaddi l1 l2 = case (l1,l2) of
    (l1,[]) => l1
  | ([],l2) => l2
  | (a1 :: m1, a2 :: m2) => a1 + a2 :: polyaddi m1 m2

fun polydiff l1 l2 = case (l1,l2) of
    (l1,[]) => l1
  | ([],l2) => polydiff (List.tabulate (length l2, fn _ => 0)) l2
  | (a1 :: m1, a2 :: m2) => a1 - a2 :: polydiff m1 m2

fun polymult l1 l2 = case (l1,l2) of 
    (l1,[]) => raise ERR "polymult" ""
  | ([],l2) => raise ERR "polymult" ""
  | (l1,[a]) => map (fn x => a * x) l1
  | ([a],l2) => map (fn x => a * x) l2
  | (a1 :: m1, l2) => 
    polyaddi (map (fn x => a1 * x) l2)  (polymult m1 (0 :: l2))

fun polydivi l1 l2 = case (l1,l2) of
    ([a],[b]) => [a div b]
  | _ => raise ERR "polydivi" ""
fun polymodu l1 l2 = case (l1,l2) of
    ([a],[b]) => [a mod b]
  | _ => raise ERR "polymodu" ""

fun polynorm prog = case prog of
    Ins (0,[]) => [0]
  | Ins (1,[]) => [1]
  | Ins (2,[]) => [2]
  | Ins (3,[p1,p2]) => polyaddi (polynorm p1) (polynorm p2)
  | Ins (4,[p1,p2]) => polydiff (polynorm p1) (polynorm p2)
  | Ins (5,[p1,p2]) => polymult (polynorm p1) (polynorm p2)
  | Ins (6,[p1,p2]) => polydivi (polynorm p1) (polynorm p2)
  | Ins (7,[p1,p2]) => polymodu (polynorm p1) (polynorm p2)
  | Ins (10,[]) => [0,1]
  | _ => raise ERR "polynorm" ""

fun string_of_mono vn (a,i) = 
  (if a = 1 andalso i <> 0 then "" else 
   if a = ~1 andalso i <> 0 then "-" else itsm a) ^
  (if (a = 1 andalso i <> 0) orelse
      (a = ~1 andalso i <> 0) orelse
      (i = 0)
   then "" else "*") ^
  (if i = 0 then "" else if i = 1 then mk_xn vn else mk_xn vn ^ 
     (if !imperative_flag then "**" else "^") ^ its i)

fun string_of_poly vn l = 
  let val l1 = filter (fn x => fst x <> 0) (number_snd 0 l) in
    if null l1 then "0" else
    let val s = String.concatWith " + " (map (string_of_mono vn) (rev l1)) in
      if length l1 = 1 then s else "(" ^ s ^ ")"
    end
  end

fun polyaddil l = case l of 
    [] => [] 
  | a :: m => polyaddi a (polyaddil m)

fun polymultl l = case l of 
    [] => raise ERR "polymultl" ""
  | [a] => a 
  | a :: m => polymult a (polymultl m)

fun rm_par s = 
  if String.size s = 0 then s else
  if String.sub (s,0) = #"(" andalso String.sub (s,String.size s - 1) =  #")" 
  then String.substring (s,1,String.size s - 2)
  else s;

fun strip_addi p = case p of
    Ins (3,[p1,p2]) => 
    let 
      val (a1,b1) = strip_addi p1 
      val (a2,b2) = strip_addi p2
    in
      (a1 @ a2, b1 @ b2)
    end 
  | Ins (4,[p1,p2]) =>
    let 
      val (a1,b1) = strip_addi p1
      val (a2,b2) = strip_addi p2
    in
      (a1 @ b2, a2 @ b1)
    end 
  | _ => ([p],[])

fun strip_mult p = case p of
    Ins (5,[p1,p2]) => strip_mult p1 @ strip_mult p2 
  | _ => [p]

(* -------------------------------------------------------------------------
   Printing to custom language or Python 
   ------------------------------------------------------------------------- *)

fun is_loop (Ins(id,pl)) = mem id [9,12,13]

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
    fun lrhx b = if !nolam_flag then rhx b else "\\(x,y)." ^ rhx b
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
    Ins (3,[p1,p2]) => 
    if !polynorm_flag then reg_add vn prog 
    else "(" ^ h p1 ^ " + " ^ h p2 ^ ")"   
  | Ins (4,[p1,p2]) =>  
    if !polynorm_flag then reg_add vn prog
    else "(" ^ h p1 ^ " - " ^ h p2 ^ ")"   
  | Ins (5,[p1,p2]) =>
    if !polynorm_flag then reg_mult vn prog
    else "(" ^ h p1 ^ " * " ^ h p2 ^ ")"
  | Ins (6,[p1,p2]) => 
    if !imperative_flag then "(" ^ h p1 ^ " // " ^ h p2 ^ ")"
    else "(" ^ h p1 ^ " div " ^ h p2 ^ ")"
  | Ins (7,[p1,p2]) => 
    if !imperative_flag then "(" ^ h p1 ^ " % " ^ h p2 ^ ")"
    else "(" ^ h p1 ^ " mod " ^ h p2 ^ ")"
  | Ins (8,[p1,p2,p3]) => 
     let fun rh p =  (h p) in
       if !imperative_flag
       then "(" ^ rh p2 ^ " if " ^ rh p1 ^ " <= 0 else " ^ rh p3 ^ ")"
       else "(if " ^ rh p1 ^ " <= 0 then " ^ rh p2  ^ " else " ^ rh p3 ^ ")"
     end
  | Ins (9,[p1,p2,p3]) => 
    if not (!imperative_flag) then
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
    if not (!imperative_flag) 
      then "compr(" ^ lrhx p1 ^ ", " ^ rhx p2 ^ ")"
    else let fun f wn = 
      let val (s1,s2) = (rhx p1, rhuman wn p2) in
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
    if not (!imperative_flag) 
      then "loop2(" ^ String.concatWith ", "
            [lrhx p1, lrhx p2, rhx p3, rhx p4, rhx p5] ^ ")"
    else let fun f wn =
      let
        val (s1,s2) = (hx p1, hx p2)
        val s3 = human wn p3 ^ " + 1"
        val (s4,s5) = (rhuman wn p4, rhuman wn p5) 
      in
        ["  x = " ^ s4,
         "  y = " ^ s5,
         "  for i in range (1," ^ s3 ^ "):",
         "    x,y = " ^ s1 ^ "," ^ s2,
         "  return x"]
      end
    in
      wrap_def f
    end
  | Ins (s,[]) => its s
  | Ins (s,l) => "(" ^ its s ^ " " ^ String.concatWith " " (map h l) ^ ")"
  end

and reg_add vn p = 
  let 
    val (pl1,pl2) = strip_addi p
    val (pl1a,pl1b) = partition (can polynorm) pl1
    val (pl2a,pl2b) = partition (can polynorm) pl2
    val pl1n = map polynorm pl1a
    val pl2n = map polynorm pl2a
    fun human_addl pl = case pl of 
         [] => raise ERR "reg_add" ""
       | [a] => human vn a 
       | _ => "(" ^ String.concatWith " + " (map (human vn) pl) ^ ")"
    val polyo = if null pl1n andalso null pl2n then NONE else 
      SOME (polydiff (polyaddil pl1n) (polyaddil pl2n)) 
  in
    case (polyo,pl1b,pl2b) of
      (NONE,[],[]) => raise ERR "reg_add 2" ""
    | (NONE,_,[]) => human_addl pl1b
    | (NONE,[],_) => "-" ^ human_addl pl2b
    | (NONE,_,_) => "(" ^ human_addl pl1b ^ " - " ^ human_addl pl2b ^ ")"
    | (SOME poly,[],[]) => string_of_poly vn poly 
    | (SOME poly,_,[]) => "(" ^ string_of_poly vn poly ^ 
      " + " ^ human_addl pl1b ^ ")"
    | (SOME poly,[],_) => "(" ^ string_of_poly vn poly ^ 
      " - " ^ human_addl pl2b ^ ")"
    | (SOME poly,_,_) => "(" ^ string_of_poly vn poly ^ 
      " + " ^ human_addl pl1b ^ " - " ^ human_addl pl2b ^ ")"
  end

and reg_mult vn p =
  let 
    val pl = strip_mult p 
    val (pla,plb) = partition (can polynorm) pl
    fun human_multl pl = case pl of 
         [] => raise ERR "reg_mult" ""
       | [a] => human vn a 
       | _ => "(" ^ String.concatWith " * " (map (human vn) pl) ^ ")"
    val polyo = if null pla then NONE else 
      SOME (polymultl (map polynorm pla))  
  in
    case (polyo,plb) of 
      (NONE,[]) => raise ERR "reg_mult 2" ""
    | (NONE,_) => human_multl plb
    | (SOME poly,[]) => string_of_poly vn poly
    | (SOME poly,_) => "(" ^ string_of_poly vn poly ^ " * " ^ 
      human_multl plb ^ ")"
  end

fun humanf p =
  let 
    val _ = imperative_flag := false
    val s = human (~1) p
  in rm_par s end

fun humani ntop p =
  let 
    val _ = imperative_flag := true
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
    val _ = imperative_flag := false
  in
    ps
  end

fun sexpr (Ins (id,pl)) =
  if null pl then its id else 
  "(" ^ String.concatWith " " (its id :: map sexpr pl) ^ ")";


(* -------------------------------------------------------------------------
   Parsing S-expressions
   ------------------------------------------------------------------------- *)

datatype sexp = Sexp of sexp list | Stoken of string;

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
  
fun parse_human_aux sexp = case sexp of
    Stoken token => Ins (dfind token tokend, [])
  | Sexp (Stoken token :: m)  => 
    Ins (dfind token tokend, map parse_human_aux m)
  | _ => raise ERR "parse_human" ""
  
fun parse_human s = parse_human_aux (parse_sexp s)
  handle HOL_ERR _ => raise ERR "parse_human" s
 
  
(*
load "rl"; open aiLib kernel human rl;
val p = random_prog 20;
print_endline (humanf p ^ "\n"); 
print_endline (humani 32 p) ;
val p = parse_human "(+ 1 1)";
*)

end (* struct *)
