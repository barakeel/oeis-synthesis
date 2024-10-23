structure smt_reader :> smt_reader =
struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "smt_reader"
type finfo = string * int * bool
type finfox = string * int * bool * string

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
   From HOL terms to first-order SML programs
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
   From HOL terms to programs in the original programming language
   -------------------------------------------------------------------------- *)

fun dfind s d = aiLib.dfind s d handle NotFound => raise ERR "dfind" s

fun find_allfun vls deftop = 
  let
    val acc = ref []
    val reserved = (["+","-","*","divf","modf","<=","ite"] @ vls)
    fun find_allfun_aux def =
      let 
        val (oper,argl) = strip_comb def 
        val opers = string_of_var oper
      in
        if mem opers reserved then () else acc := opers :: !acc;
        app find_allfun_aux argl
      end
  in
    find_allfun_aux deftop; !acc
  end

fun hol_to_prog_aux fd vls def =
  let 
    fun binop s argl =
      let val (a,b) = pair_of_list argl in 
         ["("] @ hol_to_prog_aux fd vls a @ [s] @ 
                 hol_to_prog_aux fd vls b @ [")"]
      end
    val (oper,argl) = strip_comb def
  in
    case string_of_var oper of
       "+" => binop "+" argl
     | "-" => binop "-" argl
     | "*" => binop "*" argl
     | "divf" => binop "div" argl
     | "modf" => binop "mod" argl
     | "<=" => binop "<=" argl
     | "ite" => 
       let val (a,b,c) = triple_of_list argl in
         ["(","if"] @ hol_to_prog_aux fd vls a @ 
         ["then"] @ hol_to_prog_aux fd vls b @ 
         ["else"] @ hol_to_prog_aux fd vls c @ [")"]
       end
     | s => if null argl then 
               if mem s vls then [s] else [dfind s (!fd)]
             else
              ["(", dfind s (!fd)] @ 
              List.concat (map (hol_to_prog_aux fd vls) argl) @
              [")"]
  end;

fun hol_to_prog operd fd tm = 
  let
    val (decl,def) = dest_eq (snd (strip_forall tm)) 
    val opers = string_of_var (fst (strip_comb decl))
    val vls = ["0","1","2"] @ map string_of_var (snd (strip_comb decl))
  in
    (* loop help function *)
    if hd_string opers = #"u" andalso 
       emem ("v" ^ tl_string opers) operd andalso 
       not (emem ("w" ^ tl_string opers) operd)
    then
       let 
         val recsl = find_allfun vls def
         val recs = singleton_of_list (filter (fn x => x <> opers) recsl)  
         val r = "( " ^ "loop1u" ^ " " ^ dfind recs (!fd) ^ " )"       
       in
         fd := dadd opers r (!fd)
       end
    (* loop function *)
    else if hd_string opers = #"v" andalso
       not (emem ("w" ^ tl_string opers) operd)
    then
      let val r = "( loop1 " ^ 
        String.concatWith " " (hol_to_prog_aux fd vls def) ^ " )"
      in
        fd := dadd opers r (!fd)
      end
    (* loop2 help functions *)   
    else if mem (hd_string opers) [#"u",#"v"] andalso 
      emem ("w" ^ tl_string opers) operd 
    then
       let 
         val recsl = find_allfun vls def
         val recs = singleton_of_list 
           (filter (fn x => not (mem (hd_string x) [#"u",#"v"])) recsl) 
       in
         fd := dadd opers recs (!fd)
       end 
    else if hd_string opers = #"w"
    then
       let 
         val is = tl_string opers
         val fs = dfind ("u" ^ is) (!fd)
         val gs = dfind ("v" ^ is) (!fd)
         val fdef = dfind fs (!fd)
         val gdef = dfind gs (!fd)
         val r1 = "( loop2u " ^ fdef ^ " " ^ gdef ^ " )"
         val r2 = "( loop2v " ^ fdef ^ " " ^ gdef ^ " )"
         val _ = fd := dadd ("u" ^ is) r1 (!fd)
         val _ = fd := dadd ("v" ^ is) r2 (!fd)
         val r = "( loop2 " ^ 
           String.concatWith " " (hol_to_prog_aux fd vls def) ^ " )"
      in
        fd := dadd opers r (!fd)
      end 
    else
      let
         val r = String.concatWith " " (hol_to_prog_aux fd vls def)
      in
        fd := dadd opers r (!fd)
      end
  end
  
fun clean_paren_aux charl acc = case charl of
    [] => rev acc
  | #"(" :: #" " :: m => clean_paren_aux m (#"(" :: acc)  
  | #" " :: #")" :: m => clean_paren_aux m (#")" :: acc)  
  | a :: m => clean_paren_aux m (a :: acc)   

fun clean_paren s = implode (clean_paren_aux (explode s) []) 
  
fun hol_to_progd idtml = 
  let 
    val (idl,tml) = split idtml
    val operd = enew String.compare (map #1 idl)
    val fd = ref (dempty String.compare)
  in
    app (hol_to_prog operd fd) tml; 
    dnew String.compare (map_snd clean_paren (dlist (!fd)))
  end


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
    combine (map fst l4,l3)
  end

fun read_smt_exec file =   
  let 
    val l0 = readl file
    val l1 = List.mapPartial parseLine l0; 
    val l2 = List.mapPartial get_assert l1;  
    val l3 = map smt_to_hol (butlast l2);
    val l4 = map hol_to_sml l3;
    val l5 = map fst l4
    val fd = hol_to_progd (combine (l5,l3))
    val (execl,reset_cache) = create_execl l4
  in
    map (fn ((a,b,c),e) => ((a,b,c,dfind a fd),(e,reset_cache))) 
      (combine (l5,execl))
  end

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
 
fun uncurry3 f (a,b,c) = f a b c
fun cartesian_product3 l = map triple_of_list (cartesian_productl [l,l,l]) 
  
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
    Fun0 f0 => fingerprint_aux (f0,reset_cache) [()]
  | Fun1 f1 => fingerprint_aux (f1,reset_cache) inputl1
  | Fun2 f2 => fingerprint_aux (uncurry f2, reset_cache) inputl2
  | Fun3 f3 => fingerprint_aux (uncurry3 f3, reset_cache) inputl3

fun fingerprint_file file = 
  let 
    val _ = print_endline ("Read: " ^ file);
    val l0 = read_smt_exec (selfdir ^ "/smt/" ^ file);
    val l3 = map_snd fingerprint l0
    val l4 = filter (fn (a,b) => isSome b) l3
    val l5 = map (fn (a,b) => (a,valOf b)) l4
    fun f ((a,b,c,d),l) = file ^ ".a" ^ " " ^ its b ^ " " ^ 
      (if c then "r" else "p") ^ " " ^ d ^ " : " ^ 
      String.concatWith " " (map IntInf.toString l)
  in
    String.concatWith " | " (map f l5)
  end;



end (* struct *)

(*
load "smt_reader"; open aiLib kernel smt_reader;
val l0 = read_smt_hol "smt/A83696.smt2";
val d = hol_to_progd l0;
val l = dlist d;


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
val sl = parmap_sl 40 "smt_reader.fingerprint_file" filel;
writel (selfdir ^ "/fingerprint") sl;
*)


