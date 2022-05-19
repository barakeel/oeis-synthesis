structure human :> human =
struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "human"

type prog = kernel.prog

val polynorm_flag = ref false
val imperative_flag = ref false

fun mk_xn vn = if vn = ~1 then "x" else "X"
fun mk_yn vn = if vn = ~1 then "y" else "Y"

(* -------------------------------------------------------------------------
   Polynomial normalization
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

fun human vn prog = case prog of
    Ins (3,[p1,p2]) => 
    if !polynorm_flag 
    then reg_add vn prog
    else "(" ^ human vn p1 ^ " + " ^ human vn p2 ^ ")"   
  | Ins (4,[p1,p2]) =>  
    if !polynorm_flag 
    then reg_add vn prog
    else "(" ^ human vn p1 ^ " - " ^ human vn p2 ^ ")"   
  | Ins (5,[p1,p2]) =>
    if !polynorm_flag 
    then reg_mult vn prog
    else "(" ^ human vn p1 ^ " * " ^ human vn p2 ^ ")"
  | Ins (6,[p1,p2]) => 
    if !imperative_flag
    then "(" ^ human vn p1 ^ " // " ^ human vn p2 ^ ")"
    else "(" ^ human vn p1 ^ " div " ^ human vn p2 ^ ")"
  | Ins (7,[p1,p2]) => 
    if !imperative_flag
    then "(" ^ human vn p1 ^ " % " ^ human vn p2 ^ ")"
    else "(" ^ human vn p1 ^ " mod " ^ human vn p2 ^ ")"
  | Ins (8,[p1,p2,p3]) => 
     if !imperative_flag
     then "(" ^ rm_par (human vn p2) ^ " if " ^ 
                rm_par (human vn p1) ^ " <= 0 else " ^
                rm_par (human vn p3) ^ ")"
     else "(if " ^ 
       rm_par (human vn p1) ^ " <= 0 then " ^ rm_par (human vn p2)  ^ " else " ^ 
       rm_par (human vn p3) ^ ")"
  | Ins (9,[p1,p2,p3]) => 
      let
        val wn = (!funn)
        val _ = incr funn
        val s1 = rm_par (human (~1) p1)
        val s2 = human wn p2 ^ " + 1"
        val s3 = rm_par (human wn p3)
        val fs = "f" ^ its wn
        val fprev1 = if depend_on_y prog 
          then fs ^ "(" ^ mk_xn wn ^ "," ^ mk_yn wn ^ ")"
          else fs ^ "(" ^ mk_xn wn ^ ")"
        val fprev2 = if depend_on_y prog 
          then fs ^ "(" ^ mk_xn vn ^ "," ^ mk_yn vn ^ ")"
          else fs ^ "(" ^ mk_xn vn ^ ")"
        val fs_head = "def " ^ fprev1 ^ ":"
      in
        if !imperative_flag then
          let val cs = 
            [fs_head,
             "  x = " ^ s3,
             "  " ^ "for i in range (1," ^ s2 ^ "):",
             "    x = " ^ s1,
             "  return x", ""]
          in
            ctxt := !ctxt @ cs; fprev2
          end
        else
          "loop(\\(x,y)." ^ s1  ^ ", " ^ 
          rm_par (human (~1) p2)  ^ ", " ^ rm_par (human (~1) p3) ^ ")"
      end
  | Ins (10,[]) => mk_xn vn
  | Ins (11,[]) => mk_yn vn
  | Ins (12,[p1,p2]) => 
    let
      val wn = (!funn)
      val _ = incr funn
      val s1 = rm_par (human (~1) p1)
      val s2 = rm_par (human wn p2)
      val fs = "f" ^ its wn
      val fprev1 = if depend_on_y prog 
        then fs ^ "(" ^ mk_xn wn ^ "," ^ mk_yn wn ^ ")"
        else fs ^ "(" ^ mk_xn wn ^ ")"
      val fprev2 = if depend_on_y prog 
        then fs ^ "(" ^ mk_xn vn ^ "," ^ mk_yn vn ^ ")"
        else fs ^ "(" ^ mk_xn vn ^ ")"
      val fs_head = "def " ^ fprev1 ^ ":"
    in
      if !imperative_flag then
        let val cs = [fs_head,
          "  x,i = 0,0",
          "  while i <= " ^ s2 ^ ":",
          "    if " ^ s1 ^ " <= 0:",
          "      i = i + 1",
          "    x = x + 1",
          "  return x - 1", ""]
        in
          ctxt := !ctxt @ cs; fprev2
        end
      else
        "compr(\\x." ^ s1 ^ ", " ^ rm_par (human (~1) p2) ^ ")" 
    end
  | Ins (13,[p1,p2,p3,p4,p5]) => 
    "loop2(\\(x,y)." ^ rm_par (human (~1) p1)  ^ 
       ", \\(x,y)." ^ rm_par (human (~1) p2)  ^ ", " ^ 
       rm_par (human (~1) p3) ^ ", " ^ 
       rm_par (human (~1) p4) ^ ", " ^ 
       rm_par (human (~1) p5) ^ ")"
  | Ins (s,[]) => its s
  | Ins (s,l) => "(" ^ its s ^ " " ^ 
      String.concatWith " " (map (human vn) l) ^ ")"

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
    val _ = imperative_flag := false
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

(*
load "rl"; open aiLib kernel rl;
let val p = random_prog 20 in 
  print_endline (humanf p ^ "\n"); 
  print_endline (humani p) 
end;
*)

end (* struct *)
