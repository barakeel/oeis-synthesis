structure search_term :> search_term =
struct

open HolKernel boolLib aiLib kernel progx smt_hol smt_progx smt_reader
val ERR = mk_HOL_ERR "searchnew"
exception Parse;

(* -------------------------------------------------------------------------
   Global parameters from config file
   ------------------------------------------------------------------------- *)

val ncore = string_to_int (dfind "ncore" configd) handle NotFound => 2
val smtgentim = (valOf o Real.fromString)
  (dfind "smtgentim" configd) handle NotFound => 5.0
val z3lem = string_to_int (dfind "z3lem" configd) handle NotFound => 32
val z3tim = string_to_int (dfind "z3tim" configd) handle NotFound => 1
val z3try = string_to_int (dfind "z3try" configd) handle NotFound => 20
val nonesting = ref false

(* -------------------------------------------------------------------------
   Parsing functions
   ------------------------------------------------------------------------- *)

fun split_pair c s = pair_of_list (String.tokens (fn x => x = c) s)
  handle HOL_ERR _ => raise ERR "split_pair" (Char.toString c ^ ": " ^ s)

(* -------------------------------------------------------------------------
   Term functions
   ------------------------------------------------------------------------- *)

fun list_mk_comb_err (oper,argl) = list_mk_comb (oper,argl)
  handle HOL_ERR _ => raise Parse

fun list_mk_comb_err2 (oper,argl) = list_mk_comb (oper,argl)
  handle HOL_ERR _ => raise ERR "list_mk_comb_err2" 
(term_to_string oper ^ ": " ^ String.concatWith " " (map term_to_string argl))

fun mk_varn (n,k) = mk_var (n, rpt_fun_type (k+1) alpha) 
fun auto_comb (n,tml) = list_mk_comb_err2 (mk_varn (n,length tml),tml)
val var0 = mk_varn("0",0);

fun ite_template (t1,t2,t3) =
  auto_comb ("ite", [auto_comb ("<=", [t1,var0]),t2,t3]);

val xvar = ``x:'a``;
fun is_xvar x = term_eq x xvar;

fun contain_x tm = 
  let val (oper,argl) = strip_comb tm in
    is_xvar oper orelse exists contain_x argl
  end
 
(* language dependent *)
fun is_recvar v = is_var v andalso
  mem (hd_string (string_of_var v)) [#"w",#"v",#"s"]

fun contain_rec tm = 
  let val (oper,argl) = strip_comb tm in
    is_recvar oper orelse exists contain_rec argl
  end

fun is_nested tm =
  let val (oper,argl) = strip_comb tm in 
    is_recvar oper andalso exists contain_rec argl
  end;
  
fun contain_nested tm = (not o null o (find_terms is_nested)) tm;

fun acceptable tm = contain_x tm andalso contain_rec tm

(* -------------------------------------------------------------------------
   Operator to produce SMT formulas
   Q = and, R = ==>, S = not
   ------------------------------------------------------------------------- *)

fun fake_var s = mk_var (s,``:num -> num``)

val smt_operl_term = map (fn (x,i) => mk_var (x, rpt_fun_type (i+1) alpha))
  [("0",0),("1",0),("2",0),
   ("+",2),("-",2),("*",2),("divf",2),("modf",2),
   ("ite",3)] @ 
   [fake_var "loop"] @
   map (fn x => mk_var (x, alpha)) ["x","y"] @
   map fake_var ["compr","loop2"]
  
val smt_operl_pred = 
 [mk_thy_const {Name="=", Thy="min", Ty=``:'a -> 'a -> bool``},
  mk_var ("<=",``:'a -> 'a -> bool``)];

val smt_operl_logic = [``$/\``,``$==>``,``$~``];

val smt_operl = smt_operl_term @ smt_operl_pred @ smt_operl_logic

val smt_operd = enew Term.compare smt_operl



(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

val prog_counter = ref 0
val progd = ref (eempty Term.compare)

(* -------------------------------------------------------------------------
   Available moves
   ------------------------------------------------------------------------- *)

fun is_boolty x = x = bool
fun is_alphaty x = x = alpha

fun is_termoper f = 
  let val (tyl,ty) = strip_type (type_of f) in
    is_alphaty ty
  end

fun is_predoper f =
  let val (tyl,ty) = strip_type (type_of f) in
    is_boolty ty andalso all is_alphaty tyl
  end

fun is_logicoper f = 
  let val (tyl,ty) = strip_type (type_of f) in
    is_boolty ty andalso all is_boolty tyl
  end

fun available_move (board1,board2) move = 
  if is_termoper move
    then 
      if !nonesting andalso is_recvar move andalso 
         length_geq board1 (arity_of move) andalso
         exists contain_rec (first_n (arity_of move) board1)
      then false 
      else length_geq board1 (arity_of move)
  else if is_predoper move
    then length_geq board1 (arity_of move)
  else if is_logicoper move
    then
      (* if not (null board1) then false
      else *) 
      if term_eq move ``$~`` andalso not (null board2) andalso 
          is_neg (hd board2)
        then false
      else length_geq board2 (arity_of move)
  else raise ERR "availaible_move" (term_to_string move)

fun available_movel fl board = filter (available_move board) fl

(* -------------------------------------------------------------------------
   Apply a move
   ------------------------------------------------------------------------- *)

(*
if not (null (!subtml_glob)) andalso random_real () < 0.01 
    then (random_elem (!subtml_glob) :: board1, board2)
*)

fun apply_move move (board1,board2) =
  if is_termoper move then 
    let 
      val arity = arity_of move
      val (l1,l2) = part_n arity board1
    in
      if is_var move andalso string_of_var move = "ite" 
      then (ite_template (triple_of_list l1) :: l2, board2)
      else (list_mk_comb_err2 (move, l1) :: l2, board2)
    end
  else if is_predoper move then
    let 
      val arity = arity_of move
      val (l1,l2) = part_n arity board1
    in
      (board1, list_mk_comb_err2 (move, l1) :: board2)
    end
  else if is_logicoper move then
    let 
      val arity = arity_of move
      val (l1,l2) = part_n arity board2
    in
      (board1, list_mk_comb_err2 (move, l1) :: l2)
    end
  else raise ERR "apply_move" (term_to_string move)
  
(* -------------------------------------------------------------------------
   Save a program if it is alone
   ------------------------------------------------------------------------- *)

fun save_program board = case board of
    (_, p :: _) => 
      if acceptable p
      then (incr prog_counter; progd := eadd p (!progd))
      else ()
  | _ => ()

(* -------------------------------------------------------------------------
   Distributing visits in advance according to policy part of MCTS formula
   ------------------------------------------------------------------------- *)

fun best_move distop = 
  if null distop then raise ERR "best_move" "" else
  let 
    fun loop (maxmove,maxsc) dis = case dis of
        [] => maxmove
      | ((a,b),c) :: m =>
        let val sc = b / (Real.fromInt (c + 1)) in
          if sc > maxsc then loop (a,sc) m else loop (maxmove,maxsc) m
        end
    val ((atop,btop),ctop) = hd distop
    val sctop = btop / (Real.fromInt (ctop + 1))
  in
    loop (atop,sctop) distop
  end     
     
fun inc_bestmove dis = 
  let val i = best_move dis in
    map (fn ((a,b),c) => if term_eq a i then ((a,b),c+1) else ((a,b),c)) dis
  end
 
fun split_vis nvis dis = 
  let 
    fun rm_polv ((a,b),c) = (a,c)
    fun f (_,b) =
      let val c = Real.floor (b * Real.fromInt nvis) in
        if c < 0 then 0 else if c >= nvis then nvis - 1 else c
      end
    val dis1 = map_assoc f dis 
    val missing = nvis - sum_int (map snd dis1)
    val dis2 = funpow missing inc_bestmove dis1
  in
    map rm_polv dis1
  end

(* -------------------------------------------------------------------------
   Allocate time in advance according to the prior probabilities
   ------------------------------------------------------------------------- *)  
   
fun split_tim (torg,tinc) dis = 
  let 
    fun rm_polv ((a,b),c) = (a,c)
    val sum = ref 0.0
    fun f (_,b) =
      let 
        val c = b * tinc
        val newinc = if c < 0.0 then 0.0 else if c >= tinc then tinc else c
        val neworg = torg + !sum
        val _ = sum := !sum + newinc
      in  
        (neworg,newinc)
      end
  in
    map rm_polv (map_assoc f dis)
  end

(* -------------------------------------------------------------------------
   Allocate time in advance according to the prior probabilities
   ------------------------------------------------------------------------- *) 


val temperature = 0.1 
fun create_pol ml =
  let fun f move = 
    let val r = if tmem move smt_operl_logic then 2.0 * random_real () else
      random_real ()
    in 
      Math.pow (Math.e, (1.0 / temperature) * r) 
    end
  in
    normalize_distrib (map_assoc f ml)
  end
(* -------------------------------------------------------------------------
   Search limited by number of visits or a timeout
   ------------------------------------------------------------------------- *)

datatype searchlimit = Visits of int | Seconds of real * real

fun search_move_vis rt depth fl board (move,vis) =
  if vis <= 0 then () else
  search_aux rt depth (Visits vis) fl (apply_move move board)

and search_move_tim rt depth fl board (move,(torg,tinc)) =
  if torg + tinc <= Time.toReal (Timer.checkRealTimer rt) then () else
  search_aux rt depth (Seconds (torg,tinc)) fl (apply_move move board)

and search_move rt depth lim fl board pol = case lim of
    Seconds tim =>
    app (search_move_tim rt depth fl board) (split_tim tim pol)
  | Visits vis =>
    if vis - 1 <= 0 then () else
    app (search_move_vis rt depth fl board) (split_vis (vis - 1) pol)

and search_aux rt depth lim fl board = 
  if depth >= maxproglen_treesearch then () else
  let
    val _ = save_program board   
    val pol = create_pol (available_movel fl board)
  in
    search_move rt (depth + 1) lim fl board pol
  end

fun search fl lim =
  let
    val _ = if !ngen_glob <= 0 then timeincr := init_timeincr else ()
    val _ = prog_counter := 0
    val _ = progd := eempty Term.compare
    val rt = Timer.startRealTimer ()
    val depth = 0    
    val board = ([],[])
    fun test move = not (is_var move andalso
      mem (string_of_var move) ["loop","loop2","compr"])
    val newfl = filter test fl
    val (_,t) = add_time (search_aux rt depth lim newfl) board
    val tml = elist (!progd)
  in
    print_endline (its (elength (!progd)) ^ " predicates " ^ 
      "in "  ^ rts_round 2 t ^ " seconds");
    tml
  end

fun forallxy tm = 
  let 
    val vl = [``x:'a``,``y:'a``]
    val vl' = filter (fn x => tmem x vl) (free_vars tm) 
  in
    list_mk_forall (vl',tm)
  end

fun search_smt fl t = search (smt_operl @ fl) (Seconds (0.0,t))

(* -------------------------------------------------------------------------
   Evaluating predicates
   ------------------------------------------------------------------------- *)

(* create a binary function for each loop function *)

fun eval_term fed tm input =
  let 
    val (oper,argl) = strip_comb tm
    fun binop f = 
      let val (a,b) = pair_of_list argl in
        f (eval_term fed a input, eval_term fed b input)
      end   
  in
    case string_of_var oper of
      "0" => IntInf.fromInt 0
    | "1" => IntInf.fromInt 1
    | "2" => IntInf.fromInt 2
    | "+" => binop IntInf.+
    | "-" => binop IntInf.-
    | "*" => binop IntInf.*
    | "divf" => binop IntInf.div
    | "modf" => binop IntInf.mod
    | "ite" => let val (a,b,c) = triple_of_list argl in 
                 if eval_pred fed a input
                 then eval_term fed b input
                 else eval_term fed c input
               end
    | "x" => fst input
    | "y" => snd input
    | s => 
      case dfindo oper fed of
        NONE => raise ERR "eval_term" ("operator not found: " ^ s)
      | SOME f => (
                  case argl of
                    [] => f (IntInf.fromInt 0, IntInf.fromInt 0)
                  | [a] => f (eval_term fed a input, IntInf.fromInt 0)
                  | [a,b] =>  f (eval_term fed a input, eval_term fed b input)
                  | _ => raise ERR "eval_term" "arity"
                  )
  end

and eval_pred fed tm input =
  if is_conj tm then
    let val (a,b) = dest_conj tm in
      eval_pred fed a input andalso eval_pred fed b input
    end
  else if is_neg tm then not (eval_pred fed (dest_neg tm) input)
  else if is_imp tm then 
    let val (a,b) = dest_imp tm in
      not (eval_pred fed a input) orelse eval_pred fed b input
    end
  else if is_eq tm then
    let val (a,b) = dest_eq tm in
      eval_term fed a input = eval_term fed b input
    end
  else if string_of_var (fst (strip_comb tm)) = "<=" then
    let val (a,b) = pair_of_list (snd (strip_comb tm)) in
      eval_term fed a input <= eval_term fed b input
    end
  else raise ERR "eval_pred" "not a predicate"


val inputl = 
  let 
    val l1 = List.tabulate (10,IntInf.fromInt)
    val l1b = List.tabulate (19,fn x => IntInf.fromInt (x-9))
  in
    cartesian_product l1 l1b
  end;

fun add_cache f = 
  let 
    val d = ref (dempty (cpl_compare IntInf.compare IntInf.compare)) 
    fun newf input = case dfindo input (!d) of
      NONE => 
        let val (r,b) = (f input,true) 
          handle 
              Div => (IntInf.fromInt 0,false)
            | ProgTimeout => (IntInf.fromInt 1,false)
            | Overflow => (IntInf.fromInt 1,false)
            | Empty => (IntInf.fromInt 1,false)
        in
          d := dadd input (r,b) (!d); 
          if b then r else
          if r = IntInf.fromInt 0 then raise Div else raise ProgTimeout
        end      
     | SOME (r,b) => 
       if b then r else
       if r = IntInf.fromInt 0 then raise Div else raise ProgTimeout
  in
    newf
  end

fun create_fed pp =
  let
    val fpl = get_recfpl_ws (progpair_to_progxpair_shared pp)
    val fed = dnew Term.compare 
      (map_snd (add_cache o exec_memo.mk_exec_twov) fpl)
  in
    fed
  end
  
fun true_pred fed pred =
  let
    fun f x = 
      (
      abstimer := 0;
        ( 
        eval_pred fed pred x handle
          Div => false
        | ProgTimeout => true
        | Overflow => true
        | Empty => true
        )
      )
  in
    all f inputl
  end

(* -------------------------------------------------------------------------
   Induction axiom
   ------------------------------------------------------------------------- *)

fun mk_varn (n,k) = mk_var (n, rpt_fun_type (k+1) alpha) 
fun auto_comb (n,tml) = list_mk_comb_err (mk_varn (n,length tml), tml)
val xvar = mk_var ("x",alpha)
val yvar = mk_var ("y",alpha)
val zvar = mk_var ("z",alpha)
val var0 = mk_varn("0",0);
val var1 = mk_varn("1",0);
val xvari = auto_comb ("+",[xvar,var1]);
val pvar = mk_var ("P", ``:'a -> 'a -> bool``)

val induct_axiom =
  let 
    fun fP x y = list_mk_comb_err (pvar,[x,y])
    val base_tm = mk_forall (yvar, fP var0 yvar)
    val imp_tm = list_mk_forall ([xvar,yvar],
      mk_imp (fP xvar yvar, fP xvari yvar))
    val leq = mk_var ("<=",``:'a -> 'a -> bool``)
    val cond = list_mk_comb_err (leq,[var0,xvar])
    val concl_tm = list_mk_forall ([xvar,yvar],
      mk_imp (cond, fP xvar yvar))  
  in
    mk_imp (mk_conj (base_tm,imp_tm), concl_tm)
  end

fun beta_reduce x = (rhs o concl o REDEPTH_CONV BETA_CONV) x;

fun induct_cj cj =
  let 
    val xcj = list_mk_abs ([xvar,yvar],cj)
    val sub = [{redex = pvar, residue = xcj}]
  in
    beta_reduce (subst sub induct_axiom)
  end

fun get_subtml pp =
  let
    val (px1,px2) = progpair_to_progxpair_shared pp;
    val pxxl = mk_fast_set progx_compare_size 
        (all_subprog px1 @ all_subprog px2);
    val subtml = map pxx_to_hol_aux pxxl
  in
    subtml
  end

(* -------------------------------------------------------------------------
   Translation from induction predicates to NMT
   up to 20 loops are allowed
   ------------------------------------------------------------------------- *)



val smtn_glob = length smt_operl
val macron_glob = 20

(* conversion to programs *)
fun induct_to_prog d tm = 
  let 
    val (oper,argl) = strip_comb tm 
    val opern = dfind oper d 
      handle NotFound => raise ERR "induct_to_prog" (term_to_string oper)
  in
    if opern = 8 (* ite *)
    then
      let 
        val (a,b,c) = triple_of_list argl 
        val a1 = fst (pair_of_list (snd (strip_comb a)))
      in
        Ins (opern, map (induct_to_prog d) [a1,b,c])
      end
    else Ins (opern, map (induct_to_prog d) argl)
  end;

fun unfuzzify_macro mn id = id mod mn

fun prog_to_induct v (Ins (opern,pl)) =
  let val oper = Vector.sub (v,opern) in 
    if opern = 8 
    then 
      let val (a,b,c) = triple_of_list (map (prog_to_induct v) pl) in
        ite_template (a,b,c)
      end
    else list_mk_comb_err (oper, map (prog_to_induct v) pl)
  end

(* programs to strings *)
fun uppercase id = Char.toString (Char.chr (65 + id));

fun fuzzify_macro_aux mn id = 
  let 
    val idl = 
      let 
        val l = ref [id] 
        fun loop start = 
          if start + mn >= macron_glob then () else 
          (l := start+mn :: (!l); loop (start+mn))
    
        in
          loop id; !l
        end
  in
    random_elem idl
  end
       
fun fuzzify_macro mn id = 
  if random_real () > 0.1 then id else fuzzify_macro_aux mn id;        

fun lowercase mn id = Char.toString (Char.chr (97 + 
  fuzzify_macro mn (id - smtn_glob)));

fun id_to_string mn id = 
  if id < smtn_glob then uppercase id else lowercase mn id;



fun string_to_id mn s =
  let val n = Char.ord (valOf (Char.fromString s)) in 
    if n < 97 then 
      if mem (n - 65) [9,12,13] then raise Parse else n - 65
    else (smtn_glob + unfuzzify_macro mn (n - 97))
  end;

fun idl_to_string mn idl = String.concatWith " " (map (id_to_string mn) idl);
fun string_to_idl mn s = 
  let val idsl = String.tokens Char.isSpace s in
    map (string_to_id mn) idsl
  end;
 
fun prog_to_idl (Ins (i,pl)) = i :: List.concat (map prog_to_idl pl);
fun idl_to_progl v idl = case idl of
    [] => []
  | id :: m => 
    let
      val pl = idl_to_progl v m
      val arity = arity_of (Vector.sub (v,id))
      val (pl1,pl2) = part_n arity pl
    in
      if length pl1 <> arity then raise Parse else Ins (id,pl1) :: pl2
    end
    
(* alltogether *)
fun induct_to_string d tm = 
  let val mn = dlength d - smtn_glob in
    (idl_to_string mn o prog_to_idl o induct_to_prog d) tm
  end

fun string_to_induct v s = 
  let 
    fun hd_err x = hd x handle Empty => raise Parse 
    val mn = Vector.length v - smtn_glob
  in 
    (prog_to_induct v o (hd_err o idl_to_progl v) o (string_to_idl mn)) s
  end
  
fun inductl_to_stringl pp tml = 
  let
    val recfl = get_recfl_ws (progpair_to_progxpair_shared pp)
    val d = dnew Term.compare (number_snd 0 (smt_operl @ recfl))
  in
    map (induct_to_string d) tml
  end

fun stringl_to_inductl pp sl =
  let
    val ppx = progpair_to_progxpair_shared pp
    val recfl = get_recfl_ws ppx
    val v = Vector.fromList (smt_operl @ recfl)
  in
    map (string_to_induct v) sl
  end
  
fun stringl_to_inductl_option pp sl =
  let
    val ppx = progpair_to_progxpair_shared pp
    val recfl = get_recfl_ws ppx
    val v = Vector.fromList (smt_operl @ recfl)
    fun f s = 
      let val r = string_to_induct v s in 
        if type_of r = bool then SOME r else NONE 
      end 
      handle Parse => NONE
  in
    List.mapPartial f sl
  end  

(* -------------------------------------------------------------------------
   Running Z3 with induction predicates
   ------------------------------------------------------------------------- *)

fun read_status file =
  if not (exists_file file) orelse null (readl file) 
  then "unknown"
  else String.concatWith " " (String.tokens Char.isSpace (hd (readl file)));
  
val z3_bin = selfdir ^ "/z3"

fun z3_cmd t1s t2s filein fileout = String.concatWith " "
  ["timeout",t1s,z3_bin,t2s,filein,">",fileout]

fun z3_prove filein fileout t decl inductltop =
  let 
    val inductl = map induct_cj inductltop
    val cmd = z3_cmd (its (t + 1)) ("-T:" ^ its t) filein fileout
    val _ = write_induct_pb filein decl inductl
    val _ = OS.Process.system cmd
    val _ = OS.Process.sleep (Time.fromReal 0.1)
    val s = read_status fileout
    val _ = app remove_file [filein,fileout]
  in 
    s = "unsat"
  end

fun z3_prove_tml filein fileout t tml =
  let
    val cmd = z3_cmd "1" ("-t:" ^ its t) filein fileout
    val _ = write_smt filein tml
    val _ = OS.Process.system cmd
    val s = read_status fileout
    val _ = app remove_file [filein,fileout]
  in 
    s = "unsat"
  end

(* -------------------------------------------------------------------------
   Printing pairs of programs with tags and without tags
   ------------------------------------------------------------------------- *)

fun id_to_nmt id = Char.toString (Char.chr (65 + id));
fun nmt_to_id s = Char.ord (valOf (Char.fromString s)) - 65
fun nmt_macro i = Char.toString (Char.chr (97 + i));

(* write tagged programs *)
fun vo_to_idl recd vo = case vo of 
    NONE => []
  | SOME s => if hd_string s = #"w" 
              then [dfind s recd, dfind ("s" ^ tl_string s) recd]
              else [dfind s recd];
               
fun px_to_sl recd (Insx ((i,vo),pl)) = 
  id_to_nmt i :: (vo_to_idl recd vo) @ List.concat (map (px_to_sl recd) pl);

fun px_to_string recd px = String.concatWith " " (px_to_sl recd px);

fun pp_to_stringtag pp = 
  let 
    fun create_recd ppx =
      let 
        val l1 = map string_of_var (get_recfl_ws ppx); 
        val l2 = List.tabulate (length l1, nmt_macro)
      in
        dnew String.compare (combine (l1,l2))
      end
    val ppx = progpair_to_progxpair_shared pp
    val recd = create_recd ppx
  in
    px_to_string recd (fst ppx) ^ "=" ^ px_to_string recd (snd ppx)
  end

(* read tagged programs *)
fun idl_to_pxl idl = case idl of
    [] => []
  | id :: m => 
    let
      val pl = idl_to_pxl m
      val arity = arity_of_oper id
      val (pl1,pl2) = part_n arity pl
    in
      if length pl1 <> arity then raise Parse else Ins (id,pl1) :: pl2
    end

fun stringtag_to_prog s = 
  let 
    val sl1 = String.tokens Char.isSpace s
    val sl2 = filter (fn x => Char.isUpper (valOf (Char.fromString x))) sl1
    val idl = map nmt_to_id sl2
    val pl = idl_to_pxl idl
  in
    singleton_of_list pl handle HOL_ERR _ => raise ERR "stringtag_to_prog" s
  end
  
fun stringtag_to_pp s =
  let val (s1,s2) = split_pair #"=" s in
    (stringtag_to_prog s1, stringtag_to_prog s2)
  end

(* -------------------------------------------------------------------------
   Generating random induction predicates
   ------------------------------------------------------------------------- *)

fun random_inductl pp = 
  let
    val recfl = get_recfl_ws (progpair_to_progxpair_shared pp)
    val _ = print_endline (its (length recfl) ^ " recursive functions")
    (* val _ = subtml_glob := get_subtml pp
    val _ = print_endline (its (length (!subtml_glob)) ^ " subterms") *)
    val _ = nonesting := false
    val inductl1 = search_smt recfl smtgentim
    val _ = nonesting := true
    val inductl1' = search_smt recfl smtgentim
    val _ = nonesting := false
    val inductl1'' = mk_fast_set Term.compare (inductl1 @ inductl1')
    val _ = print_endline (its (length inductl1'') ^ " merged predicates")
    val fed = create_fed pp
    val (inductl2,t) = add_time (filter (true_pred fed)) inductl1''
    val _ = print_endline (its (length inductl2) ^ 
      " true predicates in " ^ rts_round 2 t ^ " seconds")
  in
    inductl2
  end

fun ppil_to_string (pp,il) = 
  if null il then raise ERR "ppil_to_string" "empty" else
  pp_to_stringtag pp ^ ">" ^ 
  String.concatWith "|" (inductl_to_stringl pp il)

fun random_inductl_string pps =
  let 
    val pp = stringtag_to_pp pps 
    val il = random_inductl pp 
  in
    ppil_to_string (pp,il)
  end

(* -------------------------------------------------------------------------
   Proof: calling z3
   ------------------------------------------------------------------------- *)

fun z3_prove_inductl filein fileout pp inductl = 
  let
    val _ = print_endline (human.humanf (fst pp) ^ " = " ^ 
                           human.humanf (snd pp))
    val _ = print_endline "declare functions"
    val decl = create_decl pp
    val _ = print_endline (its (length decl) ^ " declarations")
    val _ = print_endline (its (length inductl) ^ " induction instances")
    fun provable t sel = 
      z3_prove filein fileout t decl sel
    fun minimize acc sel = case sel of 
        [] => String.concatWith "|" ("unsat" :: inductl_to_stringl pp acc)  
      | a :: m =>
        if not (provable z3tim (acc @ m))
        then minimize (acc @ [a]) m
        else minimize acc m
    fun loop n = 
      if n <= 0 then "unknown" else 
      let 
        val sel = random_subset z3lem inductl
        val b = z3_prove filein fileout z3tim decl sel
      in 
        if b then (print_endline "minimize"; minimize [] sel) else loop (n-1)
      end
    val r = loop z3try
  in
    print_endline ""; r
  end

fun good_pp pp = 
  let val recfl = get_recfl_ws (progpair_to_progxpair_shared pp) in
    length recfl <= 20
  end


(* -------------------------------------------------------------------------
   Proof: parsing
   ------------------------------------------------------------------------- *)

fun parse_ppil stop =
  let 
    val (i,ppil) = split_pair #":" stop
    val (s1,s2) = split_pair #">" ppil
    val pp = stringtag_to_pp s1 
    val sl = String.tokens (fn x => x = #"|") s2
    val _ = print_endline (its (length sl) ^ " induction predicates")
    val tml = stringl_to_inductl_option pp sl
    val _ = print_endline (its (length sl - length tml) ^ " parse errors")
  in
    (i,(pp,tml))
  end

(* -------------------------------------------------------------------------
   Proof output
   ------------------------------------------------------------------------- *)

fun compare_string_size (s1,s2) = cpl_compare
  Int.compare String.compare ((String.size s1,s1), (String.size s2,s2))

fun compare_lemmal (lemmal1,lemmal2) =
  compare_string_size 
    (String.concatWith "|" lemmal1, String.concatWith "|" lemmal2)

fun get_status_lemmas s = 
  let 
    val (s0,s1) = split_pair #">" s
    val sl2 = String.tokens (fn x => x = #"|") s1
    val _ = if null sl2 then raise ERR "get_status_lemmas" "" else ()  
  in
    (s0,(hd sl2,tl sl2))
  end;
  
fun string_to_lemmas s = 
  let 
    val (s0,s1) = split_pair #">" s
    val sl2 = 
      if s1 = "empty" 
      then [] 
      else String.tokens (fn x => x = #"|") s1
  in
    (s0,sl2)
  end
  
fun lemmas_to_string (s,sl) = 
  s ^ ">" ^ (if null sl then "empty" else String.concatWith "|" sl)

(* -------------------------------------------------------------------------
   Proof: main functions
   ------------------------------------------------------------------------- *)

fun z3_prove_ppil_aux (i,(pp,tml)) =
  let
    val filein = selfdir ^ "/z3_" ^ i ^ "_in.smt2"
    val fileout = selfdir ^ "/z3_" ^ i ^ "_out"
    val r = z3_prove_inductl filein fileout pp tml
  in
    pp_to_stringtag pp ^ ">" ^ r
  end 

fun z3_prove_ppil s = z3_prove_ppil_aux (parse_ppil s)

fun standard_space s = String.concatWith " " (String.tokens Char.isSpace s);

fun string_of_varconst oper =
  if is_var oper then fst (dest_var oper)
  else if is_const oper then fst (dest_const oper)
  else raise ERR "string_of_varconst" (term_to_string oper);

fun tts tm = 
  let val (oper,argl) = strip_comb tm in
    if null argl
    then string_of_varconst oper
    else "(" ^ String.concatWith " " (string_of_varconst oper :: 
         map tts argl) ^ ")"
  end 

fun human_out (s,sl) = 
  let 
    val pp = stringtag_to_pp s
    val (px1,px2) = progpair_to_progxpair_shared pp
    val tml = stringl_to_inductl pp sl
  in
    progx_to_string px1 ^ " = " ^ progx_to_string px2 ^ "\n" ^ 
    String.concatWith " | " (map tts tml)
  end
  
fun merge lold lnew =
  let 
    val setold = enew String.compare (map fst lold)
    val ldiff = filter (fn (x,_) => not (emem x setold)) lnew
    val d = ref (dempty String.compare)
    fun f (k,v) = case dfindo k (!d) of
       NONE => d := dadd k v (!d)
     | SOME oldl => if compare_lemmal (v,oldl) = LESS 
                    then d := dadd k v (!d) else ()
    val _ = app f (lold @ lnew) 
  in
    (ldiff, dlist (!d))
  end
  
  
fun tag_job l = map (fn (i,x) => its i ^ ":" ^ x) (number_fst 0 l)  
 
fun process_proofl dir l2 = 
  let
    fun log s = append_endline (dir ^ "/log") s
    fun logl l s = log (its (length l) ^ " " ^ s)
    val l3 = map get_status_lemmas l2
    val l4 = filter (fn (a,(b,c)) => b = "unsat") l3
    val l5 = map (fn (a,(b,c)) => (a,c)) l4
    val _ = logl l5 "unsat"
    val lold = if not (exists_file (dir ^ "/previous"))
               then []
               else map string_to_lemmas (readl (dir ^ "/previous"))
    val (ldiff,lmerge) = merge lold l5
    val _ = logl lold "previous"
    val _ = logl ldiff "diff"
    val _ = logl lmerge "current"
    fun tonmt (key,sl) = map (fn x => key ^ ">" ^ x) sl
    val l7 = List.concat (map tonmt lmerge)
    val _ = logl l7 "examples"
  in
    writel (dir ^ "/output") l7;
    writel (dir ^ "/diff") (map lemmas_to_string ldiff);
    writel (dir ^ "/current") (map lemmas_to_string lmerge);
    writel (dir ^ "/diff_human") (map human_out ldiff);
    writel (dir ^ "/current_human") (map human_out lmerge)
  end
  
fun z3_prove_para expname = 
  if expname = "" then raise ERR "z3_prove_para" "empty expname" else
  let
    val expdir = selfdir ^ "/exp"
    val dir = expdir ^ "/" ^ expname
    fun log s = append_endline (dir ^ "/log") s
    fun logl l s = log (its (length l) ^ " " ^ s)
    val _ = app mkDir_err [expdir,dir]
    val l1 = readl (dir ^ "/input")
    val _ = logl l1 "targets"
    val (l2,t) = add_time 
      (parmap_sl ncore "search_term.z3_prove_ppil") (tag_job l1)
  in 
    process_proofl dir l2
  end

fun gen_init expname =
  let
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = app mkDir_err [selfdir ^ "/exp", dir]
    fun log s = append_endline (dir ^ "/log") s
    fun logl l s = log (its (length l) ^ " " ^ s)
    val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sem")
    val _ = logl appl "inductive problems"
    val sl = map pp_to_stringtag (map snd appl)
    val (sl2,t) = add_time 
      (parmap_sl ncore "search_term.random_inductl_string") sl
    val _ = log ("generating time: " ^ rts t) 
  in
    writel (dir ^ "/input") sl2
  end

(* -------------------------------------------------------------------------
   Initial generation of predicates
   ------------------------------------------------------------------------- *)

fun gen_prove_string s =
  let 
    val (jobn,pps) = split_pair #":" s
    val pp = stringtag_to_pp pps
    val il = random_inductl pp
  in
    z3_prove_ppil_aux (jobn,(pp,il))
  end
  
fun gen_prove_init expname =
  let
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = app mkDir_err [selfdir ^ "/exp", dir]
    fun log s = append_endline (dir ^ "/log") s
    fun logl l s = log (its (length l) ^ " " ^ s)
    val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sem")
    val _ = logl appl "inductive problems"
    val sl1 = tag_job (map pp_to_stringtag (map snd appl))
    val (sl2,t) = add_time (parmap_sl ncore "search_term.gen_prove_string") sl1
    val _ = log ("gen_prove time: " ^ rts t) 
  in
    process_proofl dir sl2
  end

(* -------------------------------------------------------------------------
   Create inference file
   ------------------------------------------------------------------------- *)

(*
load "search_term"; 
open aiLib kernel smt_hol smt_progx search_term;
val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sem");
val sl = writel (selfdir ^ "/smt_inference") 
  (map pp_to_stringtag (map snd appl));
*)

(* -------------------------------------------------------------------------
   Removing equivalent predicates (not used)
   ------------------------------------------------------------------------- *)

fun term_compare_size (t1,t2) = cpl_compare Int.compare Term.compare
  ((term_size t1,t1), (term_size t2, t2));

fun equiv_template_one a b =
  list_mk_forall ([xvar,yvar], mk_eq (a,b))

fun equiv_template a predl =
  mk_neg (list_mk_disj (map (equiv_template_one a) predl))

fun z3quotient filein fileout inductl =
  let 
    val predl = ref []
    fun loop cand = case cand of 
       [] => !predl
     | a :: m => 
       if null (!predl) then (predl := a :: !predl; loop m) else
       let val tm = equiv_template a (!predl) in
         if z3_prove_tml filein fileout 20 [tm]
         then loop m
         else (predl := a :: !predl; loop m)
       end
  in
    loop (dict_sort term_compare_size inductl)
  end

(*
load "search_term"; 
open aiLib kernel smt_hol smt_progx search_term;
val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sem");
val (a,pp) = random_elem appl;
val l1 = random_inductl pp; 
val l1conj = filter (not o null o (find_terms is_conj)) l1;
val l1imp = filter (not o null o (find_terms is_imp_only)) l1;
val l1neg= filter (not o null o (find_terms is_neg)) l1;
val l1nest = filter (not o contain_nested) l1;
length l1; length l1nest; length l1neg; length l1imp; length l1conj;


load "search_term";
search_term.gen_prove_init "smt7";
*)


end (* struct *)
