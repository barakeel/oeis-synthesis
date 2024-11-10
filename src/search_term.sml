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

val smt_operl_term = map (fn (x,i) => mk_var (x, rpt_fun_type (i+1) alpha))
  [("0",0),("1",0),("2",0),
  ("+",2),("-",2),("*",2),("divf",2),("modf",2),
  ("ite",3),("x",0),("y",0)];
  
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
   Filter conjectures by z3
   ------------------------------------------------------------------------- *)

fun read_status file = 
  String.concatWith " " (String.tokens Char.isSpace (hd (readl file)));
  
fun z3_test1 decl cj = 
  (
  write_hol_smt "aaatest" ["(set-logic UFNIA)"] (decl @ [cj]) 
  ["(check-sat)"];
  OS.Process.system "timeout 2 ./z3 -t:40 aaatest > aaatestout";
  let val s = read_status "aaatestout" in
    if s = "unsat" then print "p" else print "."; s 
  end
  );

fun z3_test decl cj = 
  let 
    val poscj = forallxy cj
    val negcj = mk_neg (forallxy cj)
  in
    (* print_endline (term_to_string cj); *)
    (cj, (z3_test1 decl poscj, z3_test1 decl negcj))
 end

fun z3_filter decl cjl = 
  let 
    val resultl = map (z3_test decl) cjl;
    fun test (a,(b,c)) = not (mem b ["unsat"] orelse mem c ["unsat"])
  in
    map fst (filter test resultl)
  end

fun z3_prove t decl inductl = 
  let 
    val cmd = "timeout " ^ its (t + 1) ^
              " ./z3 -T:" ^ its t ^ " aaatest > aaatestout"
    val _ = write_induct_pb "aaatest" decl inductl
    val _ = OS.Process.system cmd
    val s = read_status "aaatestout"
  
  in 
    if s = "unsat" then print "p" else print "."; s
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
    fun fP x y = list_mk_comb (pvar,[x,y]);
    val base_tm = mk_forall (yvar, fP var0 yvar);
    val imp_tm = list_mk_forall ([xvar,yvar],
      mk_imp (fP xvar yvar, fP xvari yvar));
    val concl_tm = list_mk_forall ([xvar,yvar],fP xvar yvar);
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

fun get_inductl t pp = 
  let
    val ppx = progpair_to_progxpair_shared pp
    val recfl = get_recfl_ws ppx
    val cjl = search_smt recfl t
    val _  = print_endline ("\n" ^ its (length cjl) ^ " conjectures") 
    val decl = create_decl pp
  in
    z3_filter decl cjl
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

fun z3_prove_inductl pp = 
  let
    val decl = create_decl pp (* include s *) 
    val _ = print_endline (human.humanf (fst pp) ^ " = " ^ 
                           human.humanf (snd pp))
    val _ = subtml_glob := get_subtml pp
    val _ = print_endline (its (length (!subtml_glob)) ^ " subprograms") 
    val inductl = get_inductl 10.0 pp
    val _ = print_endline (its (length inductl) ^ " nontrivial conjectures") 
    fun loop n = 
      if n <= 0 then "unknown" else 
      let val r = z3_prove 10 decl (map induct_cj (random_subset 32 inductl)) in
        if r = "unsat" then "unsat" else loop (n-1)
      end
  in
    loop 10
  end


(* -------------------------------------------------------------------------
   Translation from induction predicates to NMT
   ------------------------------------------------------------------------- *)

val smtn_glob = length smt_operl

(* conversion to programs *)
fun induct_to_prog d tm = 
  let 
    val (oper,argl) = strip_comb tm 
    val opern = dfind oper d 
      handle NotFound => raise ERR "induct_to_prog" (term_to_string oper)
  in
    Ins (opern, map (induct_to_prog d) argl)
  end;

fun prog_to_induct v (Ins (opern,pl)) =
  list_mk_comb (Vector.sub (v,opern), map (prog_to_induct v) pl);

(* programs to strings *)
fun uppercase id = Char.toString (Char.chr (65 + id));
fun lowercase id = Char.toString (Char.chr (97 + id - smtn_glob));
fun id_to_string id = 
  if id < smtn_glob then uppercase id else lowercase id;
fun string_to_id s =
  let val n = Char.ord (valOf (Char.fromString s)) in 
    if n < 97 then n - 65 else (n - 97 + smtn_glob)
  end;

fun idl_to_string idl = String.concatWith " " (map id_to_string idl);
fun string_to_idl s = 
  let val idsl = String.tokens Char.isSpace s in
    map string_to_id idsl
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
      if length pl1 <> arity then raise ERR "idl_to_prog" "" else 
      Ins (id,pl1) :: pl2
    end
    
(* alltogether *)
fun induct_to_string d tm = 
  (idl_to_string o prog_to_idl o induct_to_prog d) tm;
fun string_to_induct v tm = 
  (prog_to_induct v o (hd o idl_to_progl v) o string_to_idl) tm;

fun inductl_to_stringl pp tml = 
  let
    val ppx = progpair_to_progxpair_shared pp
    val recfl = get_recfl_ws ppx
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
  
(*
load "search_term"; 
open aiLib kernel search_term smt_hol smt_progx progx;

val appl = read_anumprogpairs "smt_benchmark_progpairs"; 
val (a,pp) = random_elem appl;

val inductl = get_inductl 1.0 pp;

val sl = inductl_to_stringl pp inductl;
val inductl2 = stringl_to_inductl pp sl;
list_compare Term.compare (inductl,inductl2);
*)

end (* struct *)





