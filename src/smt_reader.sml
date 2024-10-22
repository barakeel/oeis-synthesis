structure smt_reader :> smt_reader =
struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "smt_reader"
type finfo = (string * int * bool) * string

(* --------------------------------------------------------------------------
   Parsing SMT file into S-expressions
   -------------------------------------------------------------------------- *)

datatype sexp = Atom of string | Sexp of sexp list;    

fun isComment line = String.size line >= 2 andalso 
  String.substring (line, 0, 2) = ";;";

(* Helper function to add a token to the list, only if it's not empty *)
fun addToken buf tokens = case buf of 
    [] => tokens
  | _ => (implode (rev buf)) :: tokens

(* Custom tokenizer that separates parentheses and splits by spaces *)
fun tokenize [] tokens buf = rev (addToken buf tokens)
  | tokenize (c :: cs) tokens buf =
      if Char.isSpace c then
        tokenize cs (addToken buf tokens) []
      else if c = #"(" orelse c = #")" then
        tokenize cs (String.str c :: addToken buf tokens) []
      else
        tokenize cs tokens (c :: buf) 

fun tokenizeSexp str = tokenize (explode str) [] []

(* Linear S-expression parser *)
fun parseSexp acc tokens = case tokens of
    [] => raise ERR "parseSexp" "unexpected"
  | "(" :: m => parseSexp ([] :: acc) m
  | ")" :: m => 
    (
    case acc of 
      [] => raise ERR "parseSexp" "closing parentheses"
    | [l] => Sexp (rev l)  (* ignore remaining tokens *)
    | l1 :: l2 :: lm => parseSexp ((Sexp (rev l1) :: l2) :: lm) m
    )
  | tok :: m => 
    (
    case acc of 
      [] => raise ERR "parseSexp" "missing open parentheses"
    | l :: lm => parseSexp ((Atom tok :: l) :: lm) m
    )
     
fun parseLine line =
    let val tokens = tokenizeSexp line in
      if isComment line then NONE else SOME (parseSexp [] tokens)
    end;

(* --------------------------------------------------------------------------
   From S-expressions to HOL terms
   -------------------------------------------------------------------------- *)

fun smtv_to_hol v = case v of
    Sexp [Atom x, Atom "Int"] => mk_var (x,alpha)
  | _ => raise ERR "smtv_to_hol" "not supported"
  
fun smtvl_to_hol vl = case vl of
    Sexp l => map smtv_to_hol l
  | _ => raise ERR "smtvl_to_hol" "unexpected";

fun smt_to_hol sexp = case sexp of
    Sexp [Atom "forall", vl, body] => 
    list_mk_forall (smtvl_to_hol vl, smt_to_hol body)
  | Sexp [Atom "exists", vl, body] =>
    list_mk_exists (smtvl_to_hol vl, smt_to_hol body)
  | Sexp [Atom "=", e1, e2] => mk_eq (smt_to_hol e1, smt_to_hol e2)
  | Sexp (Atom a :: el) => 
    list_mk_comb (mk_var (a, rpt_fun_type (length el + 1) alpha), map 
    smt_to_hol el)
  | Atom a => mk_var (a, alpha)
  | _ => raise ERR "smt_to_hol" "not supported";
     
fun get_assert e = case e of
    Sexp [Atom "assert",e'] => SOME e'
  | _ => NONE;


(* --------------------------------------------------------------------------
   Timed program
   -------------------------------------------------------------------------- *)

fun check_timer () = if !abstimer >= !timelimit then raise ProgTimeout else ()

local open IntInf in
  val aonem = fromInt (~1)
  val azero = fromInt 0
  val aone = fromInt 1
  val atwo = fromInt 2
  fun aincr x = x + aone
  fun adecr x = x - aone
  val maxint = fromInt (valOf (Int.maxInt))
  val minint = fromInt (valOf (Int.minInt))
  fun large_int x = x > maxint orelse x < minint
  fun arb_pow a b = if b <= azero then aone else a * arb_pow a (b-aone)
  fun pow2 b = arb_pow atwo (fromInt b)
  val maxarb = arb_pow (fromInt 10) (fromInt maxintsize)
  val minarb = ~maxarb
  val large_arb = 
    if !maxint_flag 
    then (fn x => x > maxarb orelse x < minarb)
    else (fn x => false)
end

fun mylog x = if x = 0 then 1 else IntInf.log2 x
  
fun costadd costn x1 x2 y =
  if large_int x1 orelse large_int x2 orelse large_int y then 
    if large_arb y then raise ProgTimeout else
    Int.max (mylog (IntInf.abs x1), mylog (IntInf.abs x2))
  else costn
  
fun costmul costn x1 x2 y =
  if large_int x1 orelse large_int x2 orelse large_int y then 
    if large_arb y then raise ProgTimeout else
    mylog (IntInf.abs x1) + mylog (IntInf.abs x2)
  else costn


fun tu x = (incr abstimer; check_timer (); x) 

fun tadd x1 x2 = 
  let 
    val y = IntInf.+ (x1,x2)
    val cost = costadd 1 x1 x2 y
  in
    abstimer := !abstimer + cost; check_timer (); y
  end
  
fun tmin x1 x2 = 
  let 
    val y = IntInf.- (x1,x2)
    val cost = costadd 1 x1 x2 y
  in
    abstimer := !abstimer + cost; check_timer (); y
  end  

fun tmul x1 x2 = 
  let 
    val y = IntInf.* (x1,x2)
    val cost = costmul 1 x1 x2 y
  in
    abstimer := !abstimer + cost; check_timer (); y
  end  

fun tdiv x1 x2 = 
  let 
    val y = IntInf.div (x1,x2)
    val cost = costmul 5 x1 x2 y
  in
    abstimer := !abstimer + cost; check_timer (); y
  end  
  
fun tmod x1 x2 = 
  let 
    val y = IntInf.mod (x1,x2)
    val cost = costmul 5 x1 x2 y
  in
    abstimer := !abstimer + cost; check_timer (); y
  end    
 
fun tleq x1 x2 = 
  let val y = IntInf.<= (x1,x2) in 
    incr abstimer; check_timer (); y
  end

(* --------------------------------------------------------------------------
   From HOL terms to SML programs
   -------------------------------------------------------------------------- *)

fun string_of_var x = fst (dest_var x);

fun template_cache fs ds args1 args2 defs = 
  [fs,args1,"=","case","kernel.dfindo",args2,"(","!",ds,")","of",
   "SOME","r","=>","r","|","NONE","=>","let","val","r","=",
   defs,"in",ds,":=","dadd",args2,"r","(","!",ds,")",";","r","end"];

fun decl_to_sml decl defs =
  let 
    val (oper,vl) = strip_comb decl 
    val fs = string_of_var oper
    val ds = "d" ^ fs
    val args1 = if null vl then "()" else String.concatWith " " 
      (map string_of_var vl)
    val args2 = "(" ^ String.concatWith "," (map string_of_var vl) ^ ")"
  in
    template_cache fs ds args1 args2 defs
  end;

val rec_flag = ref false  
  
fun def_to_sml vls def =
  let 
    fun binop s argl =
      let val (a,b) = pair_of_list argl in 
         ["("] @ [s] @ def_to_sml vls a @ def_to_sml vls b @ [")"]
      end
    val (oper,argl) = strip_comb def
  in
    case string_of_var oper of
       "+" => binop "tadd" argl
     | "-" => binop "tmin" argl
     | "*" => binop "tmul" argl
     | "divf" => binop "tdiv" argl
     | "modf" => binop "tmod" argl
     | "<=" => binop "tleq" argl
     | "ite" => 
       let val (a,b,c) = triple_of_list argl in
         ["(","if"] @ def_to_sml vls a @ ["then"] @ def_to_sml vls b @ 
          ["else"] @ def_to_sml vls c @ [")"]
       end
     | s => if null argl 
            then 
              if not (mem s vls)
              then (rec_flag := true; ["(",s,"(",")",")"]) 
              else ["(","tu",s,")"]
            else 
              (
              rec_flag := true;
              ["("] @ (s :: List.concat (map (def_to_sml vls) argl)) @ [")"]
              ) 
  end;
 
fun hol_to_sml tm = 
  let 
    val _ = rec_flag := false
    val (decl,def) = dest_eq (snd (strip_forall tm)) 
    val narg = length (snd (strip_comb decl))
    val opers = string_of_var (fst (strip_comb decl))
    val vls = ["0","1","2"] @ map string_of_var (snd (strip_comb decl))
    val defs = String.concatWith " " (def_to_sml vls def)
    val r = String.concatWith " " (decl_to_sml decl defs)
  in
    ((opers,narg,!rec_flag),r)
  end;
  
fun split_smll acc l = if null l then raise ERR "split_smll" "" else
  if String.isPrefix "small" (snd (hd l)) 
  then (rev (hd l :: acc), tl l)  
  else split_smll (hd l :: acc) (tl l)
  ;

datatype recfun = 
  Fun0 of unit -> IntInf.int | 
  Fun1 of (IntInf.int -> IntInf.int) | 
  Fun2 of (IntInf.int -> IntInf.int -> IntInf.int) | 
  Fun3 of (IntInf.int -> IntInf.int -> IntInf.int -> IntInf.int);
  
fun dest_fun0 x = case x of Fun0 f => f | _ => raise ERR "dest_fun0" "";
fun dest_fun1 x = case x of Fun1 f => f | _ => raise ERR "dest_fun1" "";
fun dest_fun2 x = case x of Fun2 f => f | _ => raise ERR "dest_fun2" "";
fun dest_fun3 x = case x of Fun3 f => f | _ => raise ERR "dest_fun3" "";

val funl_glob = ref []
val reset_cache_glob = ref (fn () => ())

fun combine_def sl = case sl of 
    [] => raise ERR "combine_def" ""
  | a :: m => ("fun " ^ a) :: map (fn x => "and " ^ x) m

fun assign_one (fs,narg,recb) = "Fun" ^ its narg ^ " " ^ fs 

fun unit_compare ((),()) = EQUAL
 
fun get_cmps narg = "(" ^
  (if narg = 0 then "unit_compare"
  else if narg = 1 then "IntInf.compare"
  else if narg = 2 then "cpl_compare IntInf.compare IntInf.compare"
  else if narg = 3 then 
    "triple_compare IntInf.compare IntInf.compare IntInf.compare"
  else raise ERR "get_cmps" "")
  ^ ")"

fun define_cache_cmd (fs,narg,recb) = 
  let val cmps = get_cmps narg in
    String.concatWith " " ["val","d" ^ fs,"=","ref","(","dempty",cmps,")"]
  end
  
fun reset_cache_cmd (fs,narg,recb) = 
  let val cmps = get_cmps narg in
    String.concatWith " " ["d" ^ fs,":=","(","dempty",cmps,")"]
  end
  
  
fun parse_prog idsl = 
  let 
    val (idl,sl) = split idsl
    val reset_cachel_cmd = "(" ^ String.concatWith "; " 
      (map reset_cache_cmd idl) ^ ")"
    val decls = String.concatWith " " 
      (
      ["open","smt_reader","aiLib"] @ 
      map define_cache_cmd idl @
      ["fun","reset_cache","()","=",reset_cachel_cmd] @
      combine_def sl
      )
    val assigns = String.concatWith " " 
      (
      ["reset_cache_glob",":=","reset_cache",";"] @
      ["funl_glob",":=","["] @
      [String.concatWith " ," (map assign_one idl)] @ 
      ["]"]
      )
  in
    String.concatWith " " ["let",decls,"in",assigns,"end"]
  end;
  
fun create_execl idsl = 
  (smlExecute.quse_string (parse_prog idsl); (!funl_glob,!reset_cache_glob))

(* --------------------------------------------------------------------------
   Main functions
   -------------------------------------------------------------------------- *)

fun read_smt_hol file = 
  let 
    val l0 = readl file
    val l1 = List.mapPartial parseLine l0
    val l2 = List.mapPartial get_assert l1
    val l3 = map smt_to_hol (butlast l2)
    val l4 = map hol_to_sml l3
  in
    combine (l4,l3)
  end

fun read_smt_exec file =   
  let 
    val l0 = readl file
    val l1 = List.mapPartial parseLine l0; 
    val l2 = List.mapPartial get_assert l1;  
    val l3 = map smt_to_hol (butlast l2);
    val l4 = map hol_to_sml l3;
    val (execl,reset_cache) = create_execl l4
  in
    map (fn (a,b) => (a,(b,reset_cache))) (combine (l4,execl))
  end

(* --------------------------------------------------------------------------
   Finding constant functions
   -------------------------------------------------------------------------- *)

fun catch_error f x = 
  (SOME (f x) handle
    Div => NONE
  | ProgTimeout => NONE
  | Overflow => NONE
  );

fun is_const (vo: IntInf.int option) inputl f = case inputl of 
    [] => true
  | input :: m =>
    let val r = (abstimer := 0; catch_error f input) in
      case r of
         NONE => false
       | SOME newv => (case vo of 
           NONE => is_const (SOME newv) m f
         | SOME v => if newv <> v then false else is_const vo m f)
    end
;

fun uncurry3 f (a,b,c) = f a b c;
fun cartesian_product3 l = map triple_of_list (cartesian_productl [l,l,l]); 
  
fun is_constant n (exec,reset_cache) =
  let 
    val _ = reset_cache ()
    val l = List.tabulate (n,IntInf.fromInt)
    val l' = List.tabulate (n div 2,IntInf.fromInt)
  in
    case exec of 
      Fun0 f0 => false
    | Fun1 f1 => is_const NONE l f1
    | Fun2 f2 => is_const NONE (cartesian_product l l) (uncurry f2)
    | Fun3 f3 => is_const NONE (cartesian_product3 l') (uncurry3 f3)
  end;
  


fun const_file file = 
  let 
    val _ = print_endline ("Reading programs from: " ^ file);
    val l1 = read_smt_exec (selfdir ^ "/smt/" ^ file);
    val l2 = filter (#3 o fst o fst) l1
  in
    filter (is_constant 10 o snd) l2
  end;
  




(* --------------------------------------------------------------------------
   Finger printing programs
   -------------------------------------------------------------------------- *)

fun fingerprint_aux (f,reset_cache) xltop =
  let
    fun init () = (abstimer := 0; timelimit := 100000; reset_cache ())
    fun loop acc xl = 
      (
      init ();
      if null xl orelse f (hd xl) > maxarb
      then SOME (rev acc)
      else loop (f (hd xl) :: acc) (tl xl)
      )
  in
    loop [] xltop handle
      Div => NONE
    | ProgTimeout => NONE
    | Overflow => NONE
  end;
  
val inputl1 = List.tabulate (20,IntInf.fromInt);   

val inputl2 = 
  let 
    val l1 = List.tabulate (10,IntInf.fromInt) 
    fun cmp ((a,b),(c,d)) = case IntInf.compare (a+b,c+d) of
        EQUAL => list_compare IntInf.compare ([a,b],[c,d])
      | x => x
    val l2 = dict_sort cmp (cartesian_product l1 l1)
  in
    l2
  end;
  
val inputl3 =
  let 
    val l1 = List.tabulate (5,IntInf.fromInt) 
    fun cmp ((a,b,c),(d,e,f)) = case IntInf.compare (a+b+c,d+e+f) of
        EQUAL => list_compare IntInf.compare ([a,b,c],[d,e,f])
      | x => x
    val l2 = dict_sort cmp (cartesian_product3 l1)
  in
    l2
  end;

fun fingerprint (exec,reset_cache) = case exec of 
    Fun0 f0 => raise ERR "function" "0 arguments"
  | Fun1 f1 => fingerprint_aux (f1,reset_cache) inputl1
  | Fun2 f2 => fingerprint_aux (uncurry f2, reset_cache) inputl2
  | Fun3 f3 => fingerprint_aux (uncurry3 f3, reset_cache) inputl3

fun fingerprint_file file = 
  let 
    val _ = print_endline ("Read: " ^ file);
    val l0 = read_smt_exec (selfdir ^ "/smt/" ^ file);
    val l1 = filter (fn (((a,b,c),d),e) => b > 0 andalso c) l0
    val l2 = map (fn (((a,b,c),d),e) => ((a,b),e)) l1
    val l3 = map_snd fingerprint l2 
    val l4 = filter (fn (a,b) => isSome b) l3
    val l5 = map (fn (a,b) => (a,valOf b)) l4
    fun f ((a,b),l) = a ^ " " ^ its b ^ " : " ^ 
      String.concatWith " " (map IntInf.toString l)
  in
    String.concatWith " | " (file :: map f l5)
  end;

(* --------------------------------------------------------------------------
   Finding pairs of equal subprograms
   -------------------------------------------------------------------------- *)

local open IntInf in
  val aonem = fromInt (~1)
  val azero = fromInt 0
  val aone = fromInt 1
  val atwo = fromInt 2
  fun aincr x = x + aone
  fun adecr x = x - aone
  val maxint = fromInt (valOf (Int.maxInt))
  val minint = fromInt (valOf (Int.minInt))
  fun large_int x = x > maxint orelse x < minint
  fun arb_pow a b = if b <= azero then aone else a * arb_pow a (b-aone)
  fun pow2 b = arb_pow atwo (fromInt b)
  val maxarb = arb_pow (fromInt 10) (fromInt maxintsize)
  val minarb = ~maxarb
  val large_arb = 
    if !maxint_flag 
    then (fn x => x > maxarb orelse x < minarb)
    else (fn x => false)
end; 

fun s13 (a,b,c) = a;

fun split_smll acc l = 
  if null l then raise ERR "split_smll" "" else
  if (s13 o fst o fst) (hd l) = "small"
  then (rev (hd l :: acc), tl l)  
  else split_smll (hd l :: acc) (tl l)
  ;

fun find_pairs file = 
  let 
    val _ = print_endline ("Reading programs from: " ^ file);
    val l = read_smt_exec (selfdir ^ "/smt/" ^ file);
    val (l0small,l0fast) = split_smll [] l;
    val l1small = filter (fn (((a,e,_),c),b) => 
      e = 1 andalso (mem (hd_string a) [#"v",#"w"])) l0small;
    val l1fast = filter (fn (((a,e,_),c),b) => 
      e = 1 andalso (mem (hd_string a) [#"v",#"w"])) l0fast;
    val l2small = map (fn (((a,_,_),_),b) => (a,fingerprint b)) l1small;  
    val l2fast = map (fn (((a,_,_),_),b) => (a,fingerprint b)) l1fast;  
    val ll = cartesian_product l2small l2fast;
    fun test ((a,b),(c,d)) = if b = d then SOME (a,c) else NONE;
    val ll' = List.mapPartial test ll;
  in
    append_endline (selfdir ^ "/smtpairs") 
    (file ^ ":" ^ String.concatWith " " (map (fn (a,b) => a ^ "-" ^ b) ll'))
  end;
  

end (* struct *)

(*
load "smt_reader"; open aiLib kernel smt_reader;
val l0 = read_smt_exec "smt/A28242.smt2";
val l1 = filter (fn (((a,b,c),d),e) => b <> 0 andalso c) l0;
val l2 = map (fn (((a,b,c),d),e) => ((a,b),e)) l1;
val l3 = map_snd fingerprint l2;


val f = assoc "small" l';
List.tabulate (10, fn x => (dest_fun1 f) (IntInf.fromInt x));
*)

(*
todo generate a lot of programs and create a tree for
each

load "smt_reader"; open aiLib kernel smt_reader;
val filel = listDir (selfdir ^ "/smt");
val filel' = first_n 1000 filel;

val rl = filter (not o null o snd) (map_assoc const_file filel');
length rl;


val smallf = dest_fun1 (assoc ("small",1,true) a);
val fastf = dest_fun1 (assoc ("fast",1,false) b);

(* find recursive constant functions *)

val l = read_smt_exec "A20030.smt2";
val rl = const_file "A20030.smt2";

abstimer := 0;
timelimit := 10000;
List.tabulate (10,fn x => smallf (IntInf.fromInt x));

val (a',b') = read_smt_prog "smt/A83696.smt2";
val (a,b) = read_smt_exec "smt/A83696.smt2";

*)

(*
load "smt_reader"; open aiLib kernel smt_reader;
val filel = listDir (selfdir ^ "/smt");
val sl = parmap_sl 40 "smt_reader.fingerprint_file" (random_subset 20 filel);
writel (selfdir ^ "/fingerprint_recursive") sl;
*)


