structure search_term :> search_term =
struct

open HolKernel boolLib aiLib kernel progx smt_hol smt_progx smt_reader
val ERR = mk_HOL_ERR "searchnew"

fun mk_varn (n,k) = mk_var (n, rpt_fun_type (k+1) alpha) 
fun auto_comb (n,tml) = list_mk_comb (mk_varn (n,length tml),tml)
val var0 = mk_varn("0",0);

fun ite_template (t1,t2,t3) =
  auto_comb ("ite", [auto_comb ("<=", [t1,var0]),t2,t3]);

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

val prog_counter = ref 0
val progd = ref (eempty Term.compare)

(* -------------------------------------------------------------------------
   Available moves
   ------------------------------------------------------------------------- *)

fun compatible f tml =
  let 
    val tyl1 = fst (strip_type (type_of f))
    val tyl2 = map type_of tml
    val b = length tyl1 = length tyl2 andalso 
            all (fn x => Type.compare x = EQUAL) (combine (tyl1,tyl2))
  in
    b
  end

fun available_move board move =  
  if term_eq move ``$~`` andalso not (null board) andalso is_neg (hd board)
    then false
  else if is_var move andalso mem (string_of_var move) ["loop","loop2","compr"]
    then false
  else compatible move (fst (part_n (arity_of move) board))
  
fun available_movel fl board = filter (available_move board) fl

(* -------------------------------------------------------------------------
   Apply a move
   ------------------------------------------------------------------------- *)

val subtml_glob = ref ([] : term list)

fun apply_move move board =
  if not (null (!subtml_glob)) andalso random_real () < 0.1 
  then random_elem (!subtml_glob) :: board
  else
  let 
    val arity = arity_of move
    val (l1,l2) = part_n arity board 
  in
    if is_var move andalso string_of_var move = "ite" 
    then ite_template (triple_of_list (rev l1)) :: l2
    else list_mk_comb (move,rev l1) :: l2
  end

(* -------------------------------------------------------------------------
   Save a program if it is alone
   ------------------------------------------------------------------------- *)

fun save_program board = case board of
    [p] => (incr prog_counter; progd := eadd p (!progd))
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
   
fun create_pol ml =
  normalize_distrib (map_assoc (fn _ => random_real ()) ml)

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
    val board = []
    val (_,t) = add_time (search_aux rt depth lim fl) board
  in
    print_endline ("terms: " ^ its (!prog_counter));
    print_endline ("search time: "  ^ rts_round 2 t ^ " seconds");
    elist (!progd)
  end

(* -------------------------------------------------------------------------
   Operator to produce SMT formulas
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

fun forallxy tm = 
  let 
    val vl = [``x:'a``,``y:'a``]
    val vl' = filter (fn x => tmem x vl) (free_vars tm) 
  in
    list_mk_forall (vl',tm)
  end

val xvar = ``x:'a``;
fun contain_x tm = not (null (find_terms (fn x => term_eq x xvar) tm)) 
fun contain_rec tm = not (null (get_decl_md [tm]))

fun search_smt fl t =
  let 
    val tml0 = search (smt_operl @ fl) (Seconds (0.0,t))
    val tml1 = filter (fn x => type_of x = bool) tml0 
  in
    filter (fn x => contain_x x andalso contain_rec x) tml1
  end  


(* -------------------------------------------------------------------------
   Induction axiom
   ------------------------------------------------------------------------- *)

fun mk_varn (n,k) = mk_var (n, rpt_fun_type (k+1) alpha) 
fun auto_comb (n,tml) = list_mk_comb (mk_varn (n,length tml),tml)
val xvar = mk_var ("x",alpha)
val yvar = mk_var ("y",alpha)
val zvar = mk_var ("z",alpha)
val var0 = mk_varn("0",0);
val var1 = mk_varn("1",0);
val xvari = auto_comb ("+",[xvar,var1]);
val pvar = mk_var ("P", ``:'a -> 'a -> bool``)

val induct_axiom =
  let 
    fun fP x y = list_mk_comb (pvar,[x,y])
    val base_tm = mk_forall (yvar, fP var0 yvar)
    val imp_tm = list_mk_forall ([xvar,yvar],
      mk_imp (fP xvar yvar, fP xvari yvar))
    val leq = mk_var ("<=",``:'a -> 'a -> bool``)
    val cond = list_mk_comb (leq,[var0,xvar])
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

fun get_inductl t pp = 
  search_smt (get_recfl_ws (progpair_to_progxpair_shared pp)) t

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
    else list_mk_comb (oper,map (prog_to_induct v) pl)
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

exception Parse;

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

(* -------------------------------------------------------------------------
   Find good induction predicates
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

fun z3_prove_inductl filein fileout pp = 
  let
    val _ = print_endline (human.humanf (fst pp) ^ " = " ^ 
                           human.humanf (snd pp))
    val _ = print_endline "find recursive functions"
    val recfl = get_recfl_ws (progpair_to_progxpair_shared pp)
    val _ = print_endline (its (length recfl) ^ " recursive functions")
    val _ = print_endline "declare functions"
    val decl = create_decl pp
    val _ = print_endline (its (length recfl) ^ " declarations")
    val _ = print_endline "get_subterms"
    val _ = subtml_glob := get_subtml pp
    val _ = print_endline (its (length (!subtml_glob)) ^ " subterms") 
    val _ = print_endline "create induction instances"
    val inductl = search_smt recfl 60.0
    val _ = print_endline (its (length inductl) ^ " induction instances")
    fun provable t sel = 
      z3_prove filein fileout t decl sel
    fun minimize acc sel = case sel of 
        [] => String.concatWith " | " ("unsat" :: inductl_to_stringl pp acc)  
      | a :: m =>
        if not (provable 2 (acc @ m))
        then minimize (acc @ [a]) m
        else minimize acc m
    fun loop n = 
      if n <= 0 then "unknown" else 
      let 
        val sel = random_subset 32 inductl
        val b = z3_prove filein fileout 1 decl sel
      in 
        if b then (print_endline "minimize"; minimize [] sel) else loop (n-1)
      end
    val r = loop 120
  in
    print_endline ""; r
  end


fun good_pp pp = 
  let val recfl = get_recfl_ws (progpair_to_progxpair_shared pp) in
    length recfl <= 20
  end
  
fun z3_prove_anum anum =
  let
    val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs")
    val _ = print_endline anum
    val pp = assoc anum appl
    val filein = selfdir ^ "/z3_" ^ anum ^ "_in.smt2"
    val fileout = selfdir ^ "/z3_" ^ anum ^ "_out"
    val r = z3_prove_inductl filein fileout pp
  in
    anum ^ " " ^ r 
  end

(*
load "search_term"; 
open aiLib kernel smt_progx search_term;
val appl1 = read_anumprogpairs "smt_benchmark_progpairs"
val d = enew String.compare 
  (map OS.Path.base (readl "../../oeis-smt/aind_sem"));
val appl2 = filter (fn x => emem (fst x) d) appl1;
val appl3 = filter (good_pp o snd) appl2;

val al = map fst appl3;
load "smlRedirect"; open smlRedirect;
val rl = hide_in_file (selfdir ^ "/aaa_debug") 
  (parmap_sl 50 "search_term.z3_prove_anum") al; 

writel "aaa_result" rl;

val (a,pp) = random_elem appl3;

val l0 = get_inductl 15.0 pp;
val l1 = inductl_to_stringl pp l0;
val l2 = stringl_to_inductl pp l1;
list_compare Term.compare (l0,l2);


*)


end (* struct *)





