structure mcts :> mcts =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS 
  mlNeuralNetwork smlExecScripts mlTreeNeuralNetworkAlt kernel bloom

val ERR = mk_HOL_ERR "mcts"

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val simple_search = ref false
val simple_target = ref []

val use_mkl = ref false
val use_ob = ref false
val use_para = ref false
val dim_glob = ref 64
val ncore = 13 (* 20 *)
val ntarget = 13 * 6 * 4 (* 20 * 6 * 2 *)

(* -------------------------------------------------------------------------
   Conversions betwen lists of reals/ints and strings
   ------------------------------------------------------------------------- *)

fun string_to_real x = valOf (Real.fromString x)
fun ilts x = String.concatWith " " (map its x)
fun stil x = map string_to_int (String.tokens Char.isSpace x)
fun rlts x = String.concatWith " " (map rts x)
fun strl x = map string_to_real (String.tokens Char.isSpace x)

(* -------------------------------------------------------------------------
   Parameters
   ------------------------------------------------------------------------- *)

val target_glob = ref []
val maxbigsteps = 1
val noise_flag = ref false
val noise_coeff_glob = ref 0.1
val nsim_opt = ref (NONE)
val time_opt = ref (SOME 60.0)

fun string_of_timeo () = (case !time_opt of
    NONE => "Option.NONE"
  | SOME s => "Option.SOME " ^ rts s)

fun spiky_noise () = if random_real () > 0.9 then 1.0 else 0.0
fun uniform_noise () = 1.0
val uniform_flag = ref false
fun random_noise () = random_real ()

fun mctsparam () =
  {explo_coeff = 1.0,
   noise = !noise_flag, noise_coeff = !noise_coeff_glob, 
   noise_gen = if !uniform_flag then uniform_noise else random_noise,
   nsim = !nsim_opt : int option, time = !time_opt: real option};

val coreid_glob = ref 0
val ngen_glob = ref 0

val in_search = ref false

val embd = ref (dempty Term.compare)
val seqwind = ref (eempty seq_compare)
val progwind = ref (eempty progi_compare)

val progd = ref (eempty progi_compare)
val notprogd = ref (eempty progi_compare)

val semb = ref (BoolArray.fromList [])
val use_semb = ref true
val semd = ref (eempty seq_compare)
val progsemd = ref (eempty seq_compare)

val minid = ref (dempty seq_compare)
val initd = ref (eempty progi_compare)

fun eaddi x d = d := eadd x (!d)
fun ememi x d = emem x (!d)

fun spacetime space tim = 
  Math.pow (1.414, Real.fromInt space) * Real.fromInt tim

(* -------------------------------------------------------------------------
   Main process loging function
   ------------------------------------------------------------------------- *)

val expname = ref "test"

fun log s =
  let val expdir = selfdir ^ "/exp/" ^ !expname in
    print_endline s;
    append_endline (expdir ^ "/log") s
  end

(* -------------------------------------------------------------------------
   Type abbreviations
   ------------------------------------------------------------------------- *)

type seq = kernel.seq
type prog = kernel.prog
type progi = kernel.progi
type tnn = mlTreeNeuralNetworkAlt.tnn
type 'a set = 'a Redblackset.set

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = Oper of int * int | Pair

fun postpair b a = (a,b)
fun factorial n = if n <= 0 then 1 else n * factorial (n-1);

fun oper_to_movel i oper = 
  let val a = arity_of oper in
    if is_comm i then [Oper (i,0)]
    else map (fn x => Oper (i,x)) (List.tabulate (factorial a,I))
  end

val movelg_org =
  List.concat (mapi oper_to_movel (vector_to_list operv)) @ [Pair]
   
fun id_of_move m = case m of 
    Oper (id,ord) => [id,ord]
  | Pair => [1000]

fun move_compare (m1,m2) = seq_compare (id_of_move m1, id_of_move m2)

val movelg = dict_sort move_compare movelg_org
val movev = Vector.fromList movelg
val maxmove = length movelg
val moved = dnew move_compare (number_snd 0 movelg)
fun index_of_move move = dfind move moved
fun move_of_index index = Vector.sub (movev,index)

fun string_of_move m =
  let val l = id_of_move m in
    if hd l = 1000 then "pair" else
    name_of_oper (hd l) ^ "-" ^ String.concatWith "-" (map its (tl l))
  end

fun has_arity a x = 
  case x of Oper (id,_) => arity_of_oper id = a | _ => false

val movelg_arity0 = filter (has_arity 0) movelg
val movelg_arity1 = filter (has_arity 1) movelg
val movelg_arity2 = filter (has_arity 2) movelg
val movelg_arity3 = filter (has_arity 3) movelg

(* -------------------------------------------------------------------------
   Build a list of programs
   ------------------------------------------------------------------------- *)

fun partopt_aux n acc l =
  if n <= 0 then SOME (rev acc,l)
  else if null l then NONE
  else partopt_aux (n - 1) (hd l :: acc) (tl l);

fun partopt n l = partopt_aux n [] l;

fun longereq n l =
  if n <= 0 then true else if null l then false else longereq (n-1) (tl l)

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type clause = int * progi
datatype clausex = C1 of clause | C2 of clause * clause

fun prog_to_clause p = (prog_size p, zip_prog p)
val clause_compare = cpl_compare Int.compare progi_compare

fun prog_compare_size (p1,p2) = 
  clause_compare (prog_to_clause p1, prog_to_clause p2)

fun equal_clause (a,b) = (clause_compare (a,b) = EQUAL)

fun clausex_compare (a,b) = case (a,b) of
    (C1 a', C1 b') => clause_compare (a',b')
  | (C1 _ , C2 _ ) => LESS
  | (C2 _ , C1 _ ) => GREATER
  | (C2 a', C2 b') => cpl_compare clause_compare clause_compare (a',b')

fun string_of_clause clause = humanf (unzip_prog (snd clause))
fun string_of_clausex clausex = case clausex of
    C1 a => string_of_clause a
  | C2 (a,b) => "(pair " ^ string_of_clause a ^ " " ^ string_of_clause b ^ ")"

type board = clausex list
type player = (board,move) psMCTS.player
fun string_of_board (board : board) = 
  "# " ^ String.concatWith "\n# " (map string_of_clausex board)
fun board_compare (a,b) = list_compare clausex_compare (a,b)

(* -------------------------------------------------------------------------
   Permutation of arguments
   ------------------------------------------------------------------------- *)

fun permute_triple n (a,b,c) = 
  if n = 0 then SOME (a,b,c) else
  if n = 1 then (if equal_clause (c,b) then NONE else SOME (a,c,b)) else
  if n = 2 then (if equal_clause (b,a) then NONE else SOME (b,a,c)) else
  if n = 3 then (if equal_clause (c,a) then NONE else SOME (b,c,a)) else
  if n = 4 then (if equal_clause (c,a) then NONE else SOME (c,a,b)) else
  if n = 5 then (if equal_clause (c,b) orelse equal_clause (b,a) 
                 then NONE else SOME (c,b,a)) 
  else raise ERR "permute_triple" "" 

fun permute_double n (a,b) =
  if n = 0 then SOME (a,b) else
  if n = 1 then (if equal_clause (a,b) then NONE else SOME (b,a))
  else raise ERR "permute_double" ""

(* -------------------------------------------------------------------------
   Application of a move to a board
   ------------------------------------------------------------------------- *)

val complexity_compare = cpl_compare Real.compare progi_compare

fun update_minid p (psize,pi) (sem,tim) =
  let 
    val rep = dfind sem (!minid) 
    val newrep = (spacetime psize tim, pi)
  in
    if complexity_compare (newrep,rep) = LESS
    then minid := dadd sem newrep (!minid)
    else ()
  end
  handle NotFound => ()

fun update_wind p pi sem =
  let 
    val winseql = find_wins p sem
    val b = ref false
    fun f x = if not (ememi x seqwind) 
      then (eaddi x seqwind; b := true) else ()
  in
    app f winseql;
    if !b then eaddi pi progwind else ()
  end

exception ResultP of prog;

fun check_simple_target p =
  let 
    val f = mk_exec p
    fun test (x,e) = fst (f(x,0)) = e handle Div => false
    fun loop i maxn = 
      if i >= maxn then () else
      if all test (number_fst i (!simple_target)) 
      then raise ResultP (shift_prog i p)
      else loop (i+1) maxn
  in
    loop 0 16
  end

fun is_incr newc board = case board of
    C1 c :: m => clause_compare (newc,c) <> GREATER
  | C2 (c,_) :: m => clause_compare (newc,c) <> GREATER
  | [] => true

fun exec_fun_insearch p (psize,pi) plb =
  if ememi pi progd then SOME (C1 (psize,pi) :: plb)
  else if ememi pi notprogd then NONE
  else (* unseen program *)
    case semtimo_of_prog p of 
      NONE => (eaddi pi notprogd; NONE) 
    | SOME (sem,tim) =>
      (
      if !simple_search then check_simple_target p else ();
      update_minid p (psize,pi) (sem,tim);
      if not (ememi pi initd) andalso 
         (if !use_semb then bmem sem (!semb) else ememi sem semd) 
      then (eaddi pi notprogd; NONE) 
      else (* unseen sequence *)
        (
        if not (!simple_search) then update_wind p pi sem else ();
        eaddi pi progd;
        (if !use_semb then badd sem (!semb) else eaddi sem semd); 
        SOME (C1 (psize,pi) :: plb)
        )
      )

val check_order = ref true

fun exec_fun p psize plb =
  let val pi = zip_prog p in
    if !check_order andalso not (is_incr (psize,pi) plb) then NONE 
    else if !in_search
      then exec_fun_insearch p (psize,pi) plb
      else SOME (C1 (psize,pi) :: plb)
  end
  handle Subscript => raise ERR "exec_fun" (humanf p)


fun apply_moveo move board = case move of
    Oper (id,ord) =>
    let val arity = arity_of_oper id in
      if arity = 0 then exec_fun (Ins (id,[])) 1 board
      else if arity = 1 then 
        (case partopt 1 board of SOME ([C1 (na,pia)],plb) =>
           exec_fun (Ins (id,[unzip_prog pia])) na plb  
        | _ => NONE)
      else if arity = 2 orelse arity = 3 then
        (case partopt 2 board of NONE => NONE | SOME (pla,plb) =>
        (case pla of
          [C1 cb, C1 ca] => 
          if arity <> 2 then NONE else
          let val doubleo = permute_double ord (ca,cb) in
            case doubleo of NONE => NONE | SOME ((na,pia),(nb,pib)) =>
            let 
              val (pa,pb) = (unzip_prog pia,unzip_prog pib)
              val p = Ins (id,[pa,pb])
            in
              if id = compr_id andalso depend_on_i pa then NONE else 
              exec_fun p (na + nb) plb
            end     
          end
        | [C1 cc, C2 (cb,ca)] => 
          if arity <> 3 then NONE else
          let val tripleo = permute_triple ord (ca,cb,cc) in
            case tripleo of NONE => NONE | 
              SOME ((na,pia),(nb,pib),(nc,pic)) =>
            let val p = Ins (id, map unzip_prog [pia,pib,pic]) in
              exec_fun p (na + nb + nc) plb
            end
          end
        | _ => NONE))
      else raise ERR "not supported" ""
    end
  | Pair =>
    (case partopt 2 board of NONE => NONE | SOME (pla,plb) =>
    (case pla of
       [C1 ca, C1 cb] => SOME (C2 (ca,cb) :: plb)
     | _ => NONE))

fun apply_move move board = 
  valOf (apply_moveo move board)
  handle Option => raise ERR "apply_move" "option"
       | Subscript => raise ERR "apply_move" "subscript"

(* -------------------------------------------------------------------------
   Available moves
   ------------------------------------------------------------------------- *)

fun size_of_clausex cx = case cx of
    C1 a => fst a
  | C2 (a,b) => 1 + fst a + fst b

fun size_of_board board = 
  sum_int (map size_of_clausex board) + (length board - 1)

fun is_extendable_aux board = case board of
    C1 a :: m =>
    (fst a >= size_of_board m + 2 andalso is_extendable_aux m)
  | C2 (a,b) :: m => 
    (fst a >= size_of_board m + 2 andalso is_extendable_aux m)
  | _ => true

fun extend_unary_aux board = case board of
    [] => false
  | [a] => true
  | C1 a :: m =>
    (fst a >= size_of_board m + 1 andalso extend_unary_aux m)
  | C2 (a,b) :: m => 
    (fst a >= size_of_board m + 1 andalso extend_unary_aux m)

fun is_extendable board = is_extendable_aux (rev board)
fun extend_unary board = extend_unary_aux (rev board)

fun available_move board move = isSome (apply_moveo move board)

fun available_movel board = 
  filter (available_move board) 
    (
    (if is_extendable board then movelg_arity0 else []) @
    (if extend_unary board then movelg_arity1 else []) @
     movelg_arity2 @ [Pair] @ movelg_arity3
    )

(* -------------------------------------------------------------------------
   For debugging
   ------------------------------------------------------------------------- *)

fun random_step board =
  apply_move (random_elem (available_movel board)) board

fun random_board n = funpow n random_step []
  handle Interrupt => raise Interrupt 
    | _ => random_board n

fun random_prog n = case last (random_board n) of
    C1 c => unzip_prog (snd c)
  | _ => random_prog n
  
fun apply_movel movel board = foldl (uncurry apply_move) board movel

(* -------------------------------------------------------------------------
   Board status (all the checking/caching is done during apply move now)
   ------------------------------------------------------------------------- *)

fun status_of (board : board) = Undecided

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = status_of,
  available_movel = available_movel,
  apply_move = apply_move,
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = move_compare,
  movel = movelg
  }

(* -------------------------------------------------------------------------
   Represent board as a term to give to the TNN
   ------------------------------------------------------------------------- *)

val alpha2 = rpt_fun_type 2 alpha
val alpha3 = rpt_fun_type 3 alpha

(* encoding sequences *)
val natbase = 10
val nat_cat = mk_var ("nat_cat", alpha3);
val nat_neg = mk_var ("nat_neg", alpha2);
val nat_big = mk_var ("nat_big", alpha);
fun embv_nat i = mk_var ("nat" ^ its i,alpha);
val natoperl = List.tabulate (natbase,embv_nat) @ [nat_cat,nat_neg,nat_big];

fun term_of_nat n =
  if n < 0 then mk_comb (nat_neg, term_of_nat (~ n))
  else if n > 1000000 then nat_big
  else if n < natbase then embv_nat n
  else list_mk_comb (nat_cat,
    [embv_nat (n mod natbase), term_of_nat (n div natbase)])

val seq_empty = mk_var ("seq_empty", alpha);
val seq_cat = mk_var ("seq_cat", alpha3);

fun term_of_seq seq = case seq of
    [] => seq_empty
  | a :: m => list_mk_comb 
    (seq_cat, [term_of_nat a, term_of_seq m]);

val seqoperl = natoperl @ [seq_empty,seq_cat]

(* faking two layers *)
fun cap_tm tm = 
  let val name = fst (dest_var tm) in
    mk_var ("cap_" ^ name,alpha2)
  end

fun is_capped tm = 
  let val name = fst (dest_var (fst (strip_comb tm))) in
    String.isPrefix "cap_" name
  end

fun cap_opt tm = 
  if arity_of tm <= 0 
  then NONE
  else SOME (cap_tm tm)

fun cap tm = 
  let val oper = fst (strip_comb tm) in
    mk_comb (cap_tm oper, tm)
  end

(* syntactic *)
fun term_of_prog (Ins (id,pl)) = 
  if null pl then Vector.sub (operv,id) else
  cap (list_mk_comb (Vector.sub (operv,id), map term_of_prog pl))

(* stack *)
val pair_cat = mk_var ("pair_cat",alpha3);
val stack_empty = mk_var ("stack_empty", alpha);
val stack_cat = mk_var ("stack_cat", alpha3);

fun term_of_clause clause = term_of_prog (unzip_prog (snd clause))

fun term_of_clausex clausex = case clausex of
    C1 clause => term_of_clause clause
  | C2 (a,b) => 
    cap (list_mk_comb (pair_cat, [term_of_clause a,term_of_clause b]))
fun term_of_stack_aux board = case board of 
    [] => stack_empty
  | a :: m => 
    cap (list_mk_comb (stack_cat, [term_of_clausex a,term_of_stack_aux m]));

val pair_progseq = mk_var ("pair_progseq", alpha3);

fun term_of_stack board = 
  list_mk_comb (pair_progseq, 
    [term_of_stack_aux board, cap (term_of_seq (first_n 8 (!target_glob)))])

(* policy head *)
val prepoli = mk_var ("prepoli",alpha2)
val head_poli = mk_var ("head_poli", alpha2)

fun term_of_board board = mk_comb (head_poli, 
  mk_comb (prepoli, term_of_stack board))

(* embedding dimensions *)
val operl = vector_to_list operv @ [stack_empty,stack_cat,pair_cat]
val operlcap = operl @ List.mapPartial cap_opt operl
val seqoperlcap = seqoperl @ [cap_tm seq_cat, cap_tm seq_empty]
val allcap = [pair_progseq] @ operlcap @ seqoperlcap

val operlext = allcap @ [prepoli,head_poli]
val opernd = dnew Term.compare (number_snd 0 operlext)

fun dim_std_alt oper =
  if arity_of oper = 0 
  then [0,!dim_glob] 
  else [!dim_glob * arity_of oper, !dim_glob]

fun get_tnndim () = 
  map_assoc dim_std_alt allcap @ 
    [(prepoli,[!dim_glob,!dim_glob]),(head_poli,[!dim_glob,maxmove])] 

(* -------------------------------------------------------------------------
   OpenBlas Foreign Function Interface
   Be aware that using it (use_ob := true + installing openblas) 
   creates a difficult to reproduce bug.
   It seems that updating the binary during the search creates
   a bad file descriptor
   ------------------------------------------------------------------------- *)

fun fp_op_default oper embl = Vector.fromList [100.0]
val fp_op_glob = ref fp_op_default
val biais = Vector.fromList ([1.0])

local open Foreign in

fun update_fp_op () =
  let
    val lib = loadLibrary (selfdir ^ "/tnn_in_c/ob.so");
    val fp_op_sym = getSymbol lib "fp_op";
    val cra = cArrayPointer cDouble;
    val fp_op0 = buildCall3 (fp_op_sym,(cLong,cra,cra),cVoid);
    fun fp_op oper embl =
      let 
        val n = dfind oper opernd 
        val Xv = Vector.concat (embl @ [biais])
        val X = Array.tabulate (Vector.length Xv, fn i => Vector.sub (Xv,i))
        val Y = Array.tabulate (!dim_glob,fn i => 0.0)
      in 
        fp_op0 (n,X,Y);
        Array.vector Y
      end
  in
    fp_op_glob := fp_op
  end

end (* local *)

(* -------------------------------------------------------------------------
   Create the sequence of moves that would produce a program p
   ------------------------------------------------------------------------- *)

fun inv_cmp cmp (a,b) = cmp (b,a)

fun commute (Ins (oper,argl)) = 
  if is_comm oper
  then Ins (oper, dict_sort (inv_cmp prog_compare_size) (map commute argl))
  else Ins (oper, map commute argl)

fun is_appsyn target prev move =
  case apply_moveo move prev of (* extendable not tested here *)
    NONE => false
  | SOME (C1 clause :: m) => equal_prog (target,unzip_prog (snd clause))
  | _ => false

fun invapp_move board = case board of
    [] => NONE
  | C1 topclause :: m => 
    let val target = unzip_prog (snd topclause) in 
    case target of
      Ins (_,[]) =>
      let 
        val prev = m 
        val move = valOf (List.find (is_appsyn target prev) movelg) 
          handle Option => raise ERR "invapp_move" (humanf target)
      in
        SOME (prev, move)
      end
    | Ins (_,[p1,p2]) =>
      let
        val argl = dict_sort clause_compare (map prog_to_clause [p1,p2])
        val prev = map C1 argl @ m
        val move = valOf (List.find (is_appsyn target prev) movelg) 
          handle Option => 
            (
            print_endline (string_of_board board);
            print_endline (string_of_board prev);
            print_endline (humanf p1 ^ " " ^ humanf p2);
            raise ERR "invapp_move" (string_of_board board)
            )
      in
        SOME (prev, move)
      end
    | Ins (_,[p1,p2,p3]) => 
      let 
        val (c1,c2,c3) = triple_of_list
          (dict_sort clause_compare (map prog_to_clause [p1,p2,p3]))
        val prev = C1 c1 :: C2 (c2,c3) :: m
        val move = valOf (List.find (is_appsyn target prev) movelg) 
          handle Option => raise ERR "invapp_move" (humanf target)
      in
        SOME (prev, move)
      end
    | _ => raise ERR "invapp_move" "unexpected"
    end
  | C2 (ca,cb) :: m => SOME (C1 ca :: C1 cb :: m, Pair)

fun linearize_aux acc board = case invapp_move board of
    SOME (prev,move) => linearize_aux ((prev,move) :: acc) prev
  | NONE => acc

fun linearize p = linearize_aux [] [C1 (prog_to_clause p)]

(* -------------------------------------------------------------------------
   Merging solutions from searches with different semantic quotient
   ------------------------------------------------------------------------- *)

exception Rewrite of prog;

fun rewrite_merge repd (p as Ins (id,pl)) = 
  let 
    val sem = sem_of_prog p
      handle Option => raise Rewrite p
    val newp = dfind sem (!repd) handle NotFound =>
      let
        val newpl = map (rewrite_merge repd) pl
        val newptemp = Ins (id,newpl)
      in
        repd := dadd sem newptemp (!repd);
        newptemp
      end
  in
    newp
  end

fun rewrite_winl winl =
   let 
     val i = ref 0
     val repd = ref (dempty seq_compare)
     fun f p = 
       let val newp = commute (rewrite_merge repd p) in
         if depend_on_i newp then NONE 
         else if equal_prog (p,newp) then SOME newp
         else if same_sem newp p then (incr i; SOME newp) else NONE
       end
       handle Rewrite x => (log ("rewrite_winl: " ^ humanf x); NONE)
     val r = List.mapPartial f winl
   in
     (r,!i)
   end

fun find_minirep_aux pl =
  let
    val psemtiml = map_assoc (valOf o semtimo_of_prog) pl
      handle Option => raise ERR "find_minirep" "" 
    val repd = ref (dempty seq_compare)
    fun f (p,(sem,tim)) = 
      let
        val winl = find_wins p sem
        val r = spacetime (prog_size p) tim
        val pi = zip_prog p
        val new = (r,pi)
        fun g seq =
          let val old = dfind seq (!repd) in
            if complexity_compare (new,old) = LESS
            then repd := dadd seq new (!repd)
            else ()
          end
          handle NotFound => repd := dadd seq new (!repd)
      in
        app g winl
      end
  in
    app f psemtiml;
    (dlist (!repd))   
  end

fun find_minirep_merge pl = 
  map (unzip_prog o snd o snd) (find_minirep_aux pl)

fun find_minirep_train pl = 
  let 
    val l = find_minirep_aux pl
    fun f (seq,(_,pi)) = (seq, unzip_prog pi)
  in
    map f l
  end
  handle Subscript => raise ERR "find_minirep_train" ""

fun merge_sol pl =
  let
    val _ = log ("all solutions (past + concurrent): " ^ its (length pl))
    val plmini = find_minirep_merge pl
    val pl0 = dict_sort prog_compare_size plmini
    val _ = log ("smallest representants: " ^ its (length pl0))
    val (pl1,n1) = rewrite_winl pl0
    val _ = log ("rewritten solutions: " ^ its (length pl1) ^ " " ^ its n1)
    val pl2 = map snd (find_minirep_train pl1)
    val _ = log ("rewritten representants: " ^ its (length pl2))
  in
    pl2
  end

(* -------------------------------------------------------------------------
   Merge examples from different solutions
   ------------------------------------------------------------------------- *)

fun regroup_ex bml = 
  let fun f ((board,move),d) = 
    let 
      val oldv = dfind board d handle NotFound => 
        (Vector.tabulate (maxmove, fn _ => 0))
      val movei = index_of_move move
      val newv = Vector.update (oldv, movei, Vector.sub (oldv,movei) + 1)
    in
      dadd board newv d
    end
  in
    foldl f (dempty board_compare) bml
  end

fun pol_of_progl pold board = 
  normalize_proba (map Real.fromInt (vector_to_list (dfind board pold)))

fun create_ex pold (board,_) =
  (term_of_board board, pol_of_progl pold board)

fun create_exl seqprogl =
  let 
    val zerov = Vector.tabulate (maxmove, fn _ => 0.0)
    fun f (seq,p) = 
      let
        val _ = target_glob := seq
        val bml = linearize p
        fun g (board,move) =
           let 
             val movei = index_of_move move
             val newv = Vector.update (zerov, movei, 1.0)
             val newl = vector_to_list newv
           in
             (term_of_board board, newl)
           end
      in
        map g bml    
      end
    val r = map f seqprogl
    val _ = print_endline "examples created"
  in
    r
  end

(* -------------------------------------------------------------------------
   Export examples to C
   ------------------------------------------------------------------------- *)

fun order_subtm tml =
  let
    val d = ref (dempty (cpl_compare Int.compare Term.compare))
    fun traverse tm =
      let
        val (oper,argl) = strip_comb tm
        val nl = map traverse argl
        val n = 1 + sum_int nl
      in
        d := dadd (n, tm) () (!d); n
      end
    val subtml = (app (ignore o traverse) tml; dkeys (!d))
  in
    map snd subtml
  end;

val empty_sobj = rlts (List.tabulate (!dim_glob, fn _ => 9.0))

fun linearize_ex tmobjl =
  let
    val objd = dnew Term.compare tmobjl
    val subtml = order_subtm (map fst tmobjl);
    val indexd = dnew Term.compare (number_snd 0 subtml);
    fun enc_sub x = 
      let val (oper,argl) = strip_comb x in
        dfind oper opernd :: map (fn x => dfind x indexd) argl
      end
    fun enc_obj x = dfind x objd handle NotFound => []
    fun pad_sub l = 
       ilts (l @ List.tabulate (4 - length l, fn _ => 99))
    fun pad_obj l = 
       if null l then empty_sobj else 
       rlts (l @ List.tabulate (!dim_glob - length l, fn _ => 9.0))
  in
    (String.concatWith " " (map (pad_sub o enc_sub) subtml),
     String.concatWith " " (map (pad_obj o enc_obj) subtml),
     length subtml
    )
  end;

fun export_traindata ex =
  let
    val datadir = selfdir ^ "/tnn_in_c/data"
    val _ =
      (
      erase_file (datadir ^ "/arg.txt");
      erase_file (datadir ^ "/dag.txt");
      erase_file (datadir ^ "/obj.txt");
      erase_file (datadir ^ "/size.txt");
      erase_file (datadir ^ "/arity.txt");
      erase_file (datadir ^ "/head.txt")
      )
    val noper = length operlext
    val tmobjll = ex
    val nex = length tmobjll
    val (dagl,objl,sizel) = split_triple (map linearize_ex tmobjll);
    fun find_head tm = if term_eq tm head_poli then maxmove else 0
  in
    writel (datadir ^ "/arg.txt") (map its [noper,nex,!dim_glob]);
    writel (datadir ^ "/dag.txt") dagl;
    writel (datadir ^ "/obj.txt") objl;
    writel (datadir ^ "/size.txt") (map its sizel);
    writel (datadir ^ "/arity.txt") (map (its o arity_of) operlext);
    writel (datadir ^ "/head.txt") (map (its o find_head) operlext)
  end

(* -------------------------------------------------------------------------
   TNN cache
   ------------------------------------------------------------------------- *)

fun fp_emb_either tnn oper newembl = 
  (* if !use_ob andalso !ngen_glob > 0 
  then (!fp_op_glob) oper newembl
  else *) fp_emb tnn oper newembl 
     
   
fun infer_emb_cache tnn tm =
  if is_capped tm 
  then 
    (
    Redblackmap.findKey (!embd,tm) handle NotFound =>
    let
      val (oper,argl) = strip_comb tm
      val embl = map (infer_emb_cache tnn) argl
      val (newargl,newembl) = split embl
      val emb = fp_emb_either tnn oper newembl
      val newtm = list_mk_comb (oper,newargl)
    in
      embd := dadd newtm emb (!embd); 
      (newtm,emb)
    end
    )
  else
    let
      val (oper,argl) = strip_comb tm
      val embl = map (infer_emb_cache tnn) argl
      val (newargl,newembl) = split embl
      val emb = fp_emb_either tnn oper newembl
    in
      (tm,emb)
    end

(* -------------------------------------------------------------------------
   Players
   ------------------------------------------------------------------------- *)

fun rewardf board = 0.0

fun player_uniform tnn board = 
  (0.0, map (fn x => (x,1.0)) (available_movel board))

fun player_wtnn tnn board =
  let 
    val rl = infer_tnn tnn [term_of_board board]
    val pol1 = Vector.fromList (snd (singleton_of_list rl))
    val amovel = available_movel board 
    val pol2 = map (fn x => (x, Vector.sub (pol1, index_of_move x))) amovel
  in
    (rewardf board, pol2)
  end

fun player_wtnn_cache tnn board =
  let
    (* val _ = if !debug_flag then print "." else () *)
    val _ = if dlength (!embd) > 1000000
            then embd := dempty Term.compare else ()
    val tm = term_of_stack board
    val (_,preboarde) = infer_emb_cache tnn tm
      handle NotFound => 
        raise ERR "player_wtnn_cache1" (string_of_board board)
    val prepolie = fp_emb_either tnn prepoli [preboarde]
    val pol1 = Vector.fromList (descale_out (fp_emb_either tnn head_poli 
      [prepolie]))
    val amovel = available_movel board
    val pol2 = map (fn x => (x, Vector.sub (pol1, index_of_move x))) amovel
  in
    (rewardf board, pol2)
  end

(* -------------------------------------------------------------------------
   Search
   ------------------------------------------------------------------------- *)

val player_glob = ref player_wtnn_cache

fun mctsobj tnn = 
  {game = game, mctsparam = mctsparam (), player = !player_glob tnn};

fun tree_size tree = case tree of
    Leaf => 0
  | Node (node,ctreev) => 1 + 
     sum_int (map (tree_size o #3) (vector_to_list ctreev))

(* -------------------------------------------------------------------------
   Reinforcement learning loop utils
   ------------------------------------------------------------------------- *)

fun tnn_file ngen = selfdir ^ "/exp/" ^ !expname ^ "/tnn" ^ its ngen
fun sold_file ngen = selfdir ^ "/exp/" ^ !expname ^ "/sold" ^ its ngen

fun get_expdir () = selfdir ^ "/exp/" ^ !expname

fun mk_dirs () = 
  let val expdir = selfdir ^ "/exp/" ^ !expname in
    mkDir_err (selfdir ^ "/exp");
    mkDir_err expdir;
    mkDir_err (selfdir ^ "/parallel_search");
    expdir
  end

fun update_sold ((seq,prog),sold) =
  let 
    val oldprog = dfind seq sold
  in
    if prog_compare_size (prog,oldprog) = LESS 
    then dadd seq prog sold
    else sold
  end
  handle NotFound => dadd seq prog sold

fun write_sold ngen tmpname d = 
  (
  write_progl (sold_file ngen ^ tmpname) (elist d);
  write_progl (sold_file ngen) (elist d)
  )

fun read_sold ngen = enew prog_compare (read_progl (sold_file ngen))

(* -------------------------------------------------------------------------
   training
   ------------------------------------------------------------------------- *)

val ncoretrain = 4

val schedule =
  [
   {ncore = ncoretrain, verbose = true, learning_rate = 0.03,
    batch_size = 16, nepoch = 40},
   {ncore = ncoretrain, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 10},
   {ncore = ncoretrain, verbose = true, learning_rate = 0.01,
    batch_size = 16, nepoch = 10},
   {ncore = ncoretrain, verbose = true, learning_rate = 0.007,
    batch_size = 16, nepoch = 10},
   {ncore = ncoretrain, verbose = true, learning_rate = 0.005,
    batch_size = 16, nepoch = 10}
  ];

fun read_mat acc sl = case sl of
    [] => (rev acc, [])
  | "A" :: m => (rev acc, sl)
  | x :: m => 
    let 
      val line1 = strl x
      val line2 = last line1 :: butlast line1 
      val line = Vector.fromList line2
    in
      read_mat (line :: acc) m
    end

fun read_cmatl sl = case sl of 
    [] => []
  | "A" :: m => 
    let 
      val (mat1,cont) = read_mat [] m
      val w1 = Vector.fromList mat1 
    in 
      (
      if Vector.length (Vector.sub (w1,0)) = 1
      then 
        [{a = mlNeuralNetwork.idactiv, 
          da = mlNeuralNetwork.didactiv,
          w = w1}]
      else 
        [{a = mlNeuralNetwork.tanh, 
          da = mlNeuralNetwork.dtanh,
          w = w1}]
      )
      :: read_cmatl cont
    end
  | x :: m => raise ERR "read_cmatl" x

fun read_ctnn sl = case sl of
    [] => raise ERR "read_ctnn" ""
  | "START MATRICES" :: m => read_cmatl m
  | a :: m => read_ctnn m

fun read_ctnn_fixed () = 
  let val matl = read_ctnn (readl (selfdir ^ "/tnn_in_c/tnn")) in
    dnew Term.compare (combine (operlext,matl))
  end

fun trainf tmpname =
  let 
    val sold = read_sold (!ngen_glob) 
    val _ = print_endline ("reading sold " ^ (its (elength sold)))
    (* todo: move minimization before writing sold *)
    val seqpl = find_minirep_train (elist sold)
    val _ = print_endline (its (length seqpl) ^ " minimal representants")
    val ex = create_exl (shuffle seqpl)
    val _ = print_endline (its (length ex) ^ " examples created")
  in
    if !use_mkl then
      let
        val cfile = tnn_file (!ngen_glob) ^ tmpname ^ "_C"
        val sbin = if !use_para then "./tree_para" else "./tree"
        val _= 
          (
          print_endline "exporting training data";
          export_traindata ex;
          print_endline "exporting end";
          OS.Process.sleep (Time.fromReal 1.0);
          cmd_in_dir (selfdir ^ "/tnn_in_c") 
          (sbin ^ " > " ^ cfile)
          )
        val _ = OS.Process.sleep (Time.fromReal 1.0)
        (* val _ = if !use_ob then 
          cmd_in_dir (selfdir ^ "/tnn_in_c") ("sh compile_ob.sh")
          else () *)
        val matl = read_ctnn (readl cfile)
        val tnn = dnew Term.compare (combine (operlext,matl))
      in
        write_tnn (tnn_file (!ngen_glob) ^ tmpname) tnn;
        write_tnn (tnn_file (!ngen_glob)) tnn
      end
    else
    let
      val tnndim = get_tnndim ()
      val (tnn,t) = add_time (train_tnn schedule (random_tnn tnndim)) 
        (part_pct 1.0 (shuffle ex))
    in
      write_tnn (tnn_file (!ngen_glob) ^ tmpname) tnn;
      write_tnn (tnn_file (!ngen_glob)) tnn
    end
  end

fun wrap_trainf ngen tmpname =
  let
    val scriptfile = !buildheap_dir ^ "/train.sml" 
    val makefile = !buildheap_dir ^ "/Holmakefile"
  in
    writel makefile ["INCLUDES = " ^ selfdir]; 
    writel scriptfile
    ["open mcts;",
     "expname := " ^ mlquote (!expname) ^ ";",
     "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir) ^ ";",
     "mcts.ngen_glob := " ^ its (!ngen_glob) ^ ";",
     "mcts.dim_glob := " ^ its (!dim_glob) ^ ";",
     "mcts.use_mkl := " ^ bts (!use_mkl) ^ ";",
     "mcts.use_para := " ^ bts (!use_para) ^ ";",
     "mcts.use_ob := " ^ bts (!use_ob) ^ ";",
     "bloom.init_od ();",
     "trainf " ^ mlquote tmpname];
     exec_script scriptfile
  end

(* -------------------------------------------------------------------------
   Minimizing solutions using an initialized minid
   ------------------------------------------------------------------------- *)

fun minimize p =
  let 
    val sem = sem_of_prog p 
      handle Option => raise ERR "minimize" ""
    val (Ins (id,pl)) = (unzip_prog o snd o (dfind sem)) (!minid) 
      handle NotFound => p
  in
    Ins (id, map minimize pl)
  end

fun minimize_winl winl =
   let 
     val i = ref 0
     fun f p = 
       if not (is_executable p) then raise ERR "minimize_winl" (humanf p) else
       let val newp = commute (minimize p) in
         if equal_prog (p,newp) orelse depend_on_i newp then p
         else if same_sem newp p then (incr i; newp) else p
       end
     val r = map f winl
   in
     (r,!i)
   end

(* -------------------------------------------------------------------------
   Initialized dictionaries with previous solutions and their subterms
   ------------------------------------------------------------------------- *)

fun zerob b =
  let 
    val n = BoolArray.length b
    fun loop i = 
      if i >= n then () else 
      (BoolArray.update (b,i,false); loop (i+1))
  in
    loop 0
  end

val use_cache = ref false

fun init_dicts pl =
  let
    val _ = if not (!use_cache) then () else 
      let 
        fun test p = (check_simple_target p; NONE) 
          handle ResultP newp => SOME newp
        val plsol = List.mapPartial test pl 
      in
        if null plsol then () else 
        raise ResultP (hd (dict_sort prog_compare_size plsol))
      end
    val pil = map zip_prog pl
    val psemtiml = map_assoc (valOf o semtimo_of_prog) pl
      handle Option => raise ERR "init_dicts" ""  
    val seml = map (fst o snd) psemtiml
    fun g (p,(sem,tim)) = 
      (sem, (spacetime (prog_size p) tim, zip_prog p))
  in
    progd := eempty progi_compare;
    notprogd := eempty progi_compare;
    if !use_semb then 
       (semb := BoolArray.tabulate (bmod, fn _ => false);
        zerob (!semb)) 
    else semd := eempty seq_compare;
    embd := dempty Term.compare;
    seqwind := eempty seq_compare;
    progwind := eempty progi_compare;
    initd := enew progi_compare pil;
    minid := dnew seq_compare (map g psemtiml)
  end

(* -------------------------------------------------------------------------
   Main search function
   ------------------------------------------------------------------------- *)

val wnoise_flag = ref false

fun search tnn coreid =
  let
    val _ = print_endline "initialization"
    val _ = coreid_glob := coreid
    val _ = player_glob := player_wtnn_cache
    val sold = if !ngen_glob <= 0
               then eempty prog_compare
               else read_sold (!ngen_glob - 1)
    val _ = noise_flag := false
    val _ = if !coreid_glob mod 2 = 0 
            then (noise_flag := true; noise_coeff_glob := 0.1) else ()
    val (targetseq,seqnamel) = random_elem (dlist (!odname_glob))
    val _ = target_glob := targetseq
    val _ = print_endline 
      ("target: " ^ String.concatWith "-" seqnamel ^ ": " ^ 
        string_of_seq (!target_glob));
    val _ = init_dicts (elist sold)
    val _ = in_search := true
    val _ = avoid_lose := true
    val tree = starting_tree (mctsobj tnn) []
    val _ = print_endline "start search"
    val (newtree,t) = add_time (mcts (mctsobj tnn)) tree
    val _ = print_endline "end search"
    val n = tree_size newtree
    val _ = avoid_lose := false
    val _ = in_search := false
    val winl = map unzip_prog (elist (!progwind))
    val (minwinl,minn) = minimize_winl winl
    val _ = if emem (!target_glob) (!seqwind)
      then print_endline "target acquired"
      else print_endline "target missed"
  in
    print_endline ("search time: "  ^ rts_round 2 t ^ " seconds");
    print_endline ("tree_size: " ^ its n);
    print_endline ("prog sol: " ^ its (elength (!progwind)));
    print_endline ("prog mini: " ^ its minn);
    print_endline ("seq sol: " ^ its (elength (!seqwind)));
    minwinl
  end

val parspec : (tnn,int,prog list) extspec =
  {
  self_dir = selfdir,
  self = "mcts.parspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["bloom.init_od ()",
     "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir), 
     "mcts.expname := " ^ mlquote (!expname),
     "mcts.ngen_glob := " ^ its (!ngen_glob),
     "mcts.coreid_glob := " ^ its (!coreid_glob),
     "mcts.dim_glob := " ^ its (!dim_glob),
     "mcts.time_opt := " ^ string_of_timeo (),
     "mcts.use_ob := " ^ bts (!use_ob)
   ] 
    ^ ")"),
  function = search,
  write_param = write_tnn,
  read_param = read_tnn,
  write_arg = let fun f file arg = writel file [its arg] in f end,
  read_arg = let fun f file = string_to_int (hd (readl file)) in f end,
  write_result = write_progl,
  read_result = read_progl
  }

fun search_target_aux (tnn,sold) tim target =
  let
    val _ = simple_search := true
    val _ = time_opt := SOME tim;
    val _ = player_glob := player_wtnn_cache
    val _ = simple_target := target
    val _ = target_glob := target
    val _ = init_dicts (elist sold)
    val _ = in_search := true
    val _ = avoid_lose := true
    val tree = starting_tree (mctsobj tnn) []
    val (newtree,t) = add_time (mcts (mctsobj tnn)) tree
    val _ = avoid_lose := false
    val _ = in_search := false
  in
    NONE
  end
  handle ResultP p => SOME (minimize p)

fun parsearch_target tim target =
  let 
    val tnn = read_tnn (selfdir ^ "/main_tnn")
    val sold = enew prog_compare (read_progl (selfdir ^ "/main_sold"))
    val (p,t) = add_time (search_target_aux (tnn,sold) tim) target 
  in
    (true,humanf (valOf p),t) handle Option => (false, "", t)
  end

val partargetspec : (real, seq, bool * string * real) extspec =
  {
  self_dir = selfdir,
  self = "mcts.partargetspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["bloom.init_od ()",
     "smlExecScripts.buildheap_dir := " ^ mlquote (!buildheap_dir),
     "mcts.use_semb := " ^ bts (!use_semb),
     "mcts.use_ob := " ^ bts (!use_ob)
    ] 
    ^ ")"),
  function = parsearch_target,
  write_param = let fun f file param = writel file [rts param] in f end,
  read_param =  let fun f file = string_to_real (hd (readl file)) in f end,
  write_arg = let fun f file arg = writel file [ilts arg] in f end,
  read_arg = let fun f file = stil (hd (readl file)) in f end,
  write_result = let fun f file (b,s,t) = writel file [bts b, s, rts t] 
     in f end,
  read_result = let fun f file = 
       let val (s1,s2,s3) = triple_of_list (readl file) in 
         (string_to_bool s1, s2, string_to_real s3)
       end
     in f end
  }

fun parsearch_targetl ncore tim targetl =
  (
  buildheap_options := "--maxheap 10000";
  parmap_queue_extern ncore partargetspec tim targetl
  )

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun human_progseq p = 
  let 
    val seq = seq_of_prog p
    val seql = find_wins p seq
    val _ = if null seql 
      then log ("Error: human_progseq 1: " ^ (humanf p)) else ()
    fun f x = String.concatWith "-" (dfind x (!odname_glob)) ^ ": " ^ 
      String.concatWith " " (map its x)
  in
    humanf p ^ "\n" ^ String.concatWith "\n" (map f seql)
  end
  handle Interrupt => raise Interrupt | _ => 
    (log ("Error: human_progseq 2: " ^ (humanf p)); "")

fun human_progfreq (prog,freq) = its freq ^ ": " ^ humanf prog;

fun compute_freq f sol1 =
  let val freql = dlist 
    (count_dict (dempty prog_compare) (List.concat (map f sol1)))
  in
    dict_sort compare_imax freql
  end

fun stats_sol prefix sol =
  let
    val solsort = dict_sort prog_compare_size sol
    val freql1 = compute_freq all_subprog sol
    val freql2 = compute_freq under_lambda sol
  in
    polynorm_flag := false;
    writel (prefix ^ "prog") (map human_progseq solsort);
    writel (prefix ^ "freq") (map human_progfreq freql1);  
    writel (prefix ^ "freqlam") (map human_progfreq freql2);
    polynorm_flag := true;
    writel (prefix ^ "prog_poly") (map human_progseq solsort);
    writel (prefix ^ "freq_poly") (map human_progfreq freql1);
    writel (prefix ^ "freqlam_poly") (map human_progfreq freql2)
  end

fun stats_ngen dir ngen =
  let 
    val solprev = 
      if ngen = 0 then [] else #read_result parspec (sold_file (ngen - 1))
    val solnew = #read_result parspec (sold_file ngen)
    val prevd = enew prog_compare solprev
    val soldiff = filter (fn x => not (emem x prevd)) solnew
  in
    stats_sol (dir ^ "/full_") solnew;
    stats_sol (dir ^ "/diff_") soldiff
  end
  handle Interrupt => raise Interrupt | _ => log ("Error: stats_ngen")

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_search_only tmpname ngen =
  let 
    val expdir = mk_dirs ()
    val _ = log ("Search " ^ its ngen)
    val _ = buildheap_dir := expdir ^ "/search" ^ its ngen ^ tmpname;
    val _ = mkDir_err (!buildheap_dir)
    val _ = ngen_glob := ngen
    val _ = buildheap_options := "--maxheap 15000"
    val loop2_tm = Vector.sub (operv,13)
    val tnn = if ngen <= 0 
              then random_tnn (get_tnndim ())
              else read_tnn (tnn_file (ngen - 1))
    val sold = if ngen <= 0
               then eempty prog_compare
               else read_sold (ngen - 1)
    val (progll,t) = add_time
      (parmap_queue_extern ncore parspec tnn) 
         (List.tabulate (ntarget,I))
    val _ = log ("search time: " ^ rts_round 6 t)
    val _ = log ("solutions for each core:")
    val _ = log (String.concatWith " " (map (its o length) progll))
    val seqd = enew seq_compare (mapfilter seq_of_prog (elist sold))
    fun is_new p = not (emem (seq_of_prog p) seqd) 
      handle Interrupt => raise Interrupt | _ => false
    val newprogll = map (filter is_new) progll
    val _ = log ("new solutions for each core:")
    val _ = log (String.concatWith " " (map (its o length) newprogll))
    val progl = mk_fast_set prog_compare (
      List.concat progll @ elist sold)
    val newsold = enew prog_compare (merge_sol progl)
  in
    write_sold ngen tmpname newsold;
    stats_ngen (!buildheap_dir) ngen
  end

and rl_search tmpname ngen = 
  (rl_search_only tmpname ngen; rl_train tmpname ngen)

and rl_train_only tmpname ngen =
  let
    val expdir = mk_dirs ()
    val _ = log ("Train " ^ its ngen)
    val _ = buildheap_dir := expdir ^ "/train" ^ its ngen ^ tmpname
    val _ = mkDir_err (!buildheap_dir)
    val _ = buildheap_options := "--maxheap 100000"
    val _ = ngen_glob := ngen
    val (_,t) = add_time (wrap_trainf ngen) tmpname 
    val _ = log ("train time: " ^ rts_round 6 t)
  in
    ()
  end

and rl_train tmpname ngen = 
  (rl_train_only tmpname ngen; rl_search tmpname (ngen + 1))

end (* struct *)


(*
  -------------------------------------------------------------------------
  Train oeis-synthesis
  ------------------------------------------------------------------------- 

(* training *)
load "mcts"; open mcts;
expname := "run102";
time_opt := SOME 600.0;
use_mkl := true;
bloom.init_od ();
rl_train "_test12" 99;

(* testing *)
load "mcts"; open mcts; open aiLib; open kernel;
time_opt := SOME 60.0;
val tnn = mlTreeNeuralNetworkAlt.random_tnn (get_tnndim ());
bloom.init_od ();
use_semb := true;
val x = search tnn 0;
val sol1 = x;
val ntot1 = sum_int (map prog_size sol1);

(* making definitions *)
load "mcts"; open mcts; open aiLib; open kernel;
PolyML.print_depth 0;
val sol = read_progl "main_sold";
val sol = read_progl "exp/run102/sold139";
val (defl, patsol) = nbest_def 30 sol;
PolyML.print_depth 40;

map snd defl = List.tabulate (30, fn x => x + 14);
write_progl "pat" (map fst defl);
write_progl "patsol" patsol; (* mv patsol to sold139 *)


*)
