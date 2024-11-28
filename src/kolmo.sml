structure kolmo :> kolmo =
struct

open HolKernel Abbrev boolLib aiLib kernel progx smt_hol smt_progx
val ERR = mk_HOL_ERR "kolmo";

fun mk_varn (n,k) = mk_var (n, rpt_fun_type (k+1) alpha) 
fun auto_comb (n,tml) = list_mk_comb (mk_varn (n,length tml),tml)
val var0 = mk_varn("0",0);
fun ite_template (t1,t2,t3) =
  auto_comb ("ite", [auto_comb ("<=", [t1,var0]),t2,t3]);
  
(* -------------------------------------------------------------------------
   Datastructures
   ------------------------------------------------------------------------- *)

val inputl = 
  let 
    val l1 = List.tabulate (10,I)
    val l1b = List.tabulate (15,fn x => x-5)
  in
    cartesian_product l1 l1b
  end

val nullaryl_glob = map_fst (fn (x,i) => mk_var (x, rpt_fun_type (i+1) alpha))
  [(("0",0), let fun f i x = 0 in f end),
   (("1",0), let fun f i x = 1 in f end),
   (("2",0), let fun f i x = 2 in f end),
   (("x",0), let fun f i (x,y) = x in f end),
   (("y",0), let fun f i (x,y) = y in f end)];

val binaryl_glob = map_fst (fn (x,i) => mk_var (x, rpt_fun_type (i+1) alpha))
  [(("+",2), let fun f (i:int) (a,b) = a + b in f end),
   (("-",2), let fun f (i:int) (a,b) = a - b in f end),
   (("*",2), let fun f (i:int) (a,b) = a * b in f end),
   (("divf",2), let fun f (i:int) (a,b) = a div b in f end),
   (("modf",2), let fun f (i:int) (a,b) = a mod b in f end)];
   
val ternaryl_glob = map_fst (fn (x,i) => mk_var (x, rpt_fun_type (i+1) alpha))
  [(("ite",3), let fun f (i:int) (a:int,b:int,c:int) = 
     if a <= 0 then b else c in f end)];
  

fun numpart k n = number_partition k n handle HOL_ERR _ => [];

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val qd = ref (eempty (list_compare Int.compare))
val seld = ref (dempty Int.compare)
val mem_glob = ref []

(* -------------------------------------------------------------------------
   Computing and saving results
   ------------------------------------------------------------------------- *)

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

fun store_seqtm (seq,(tm:term)) =
  if is_nested tm then () else
  if emem seq (!qd) then () else
  (mem_glob := (seq,tm) :: !mem_glob; qd := eadd seq (!qd))

fun unf (oper, exec: int -> int -> int) (seq,tm) =
  let 
    val seqo = SOME (mapi exec seq) handle Div => NONE | Overflow => NONE
  in
    case seqo of NONE => () | SOME seq => 
    store_seqtm (seq,list_mk_comb (oper,[tm]))
  end

fun binf (oper, exec: int -> int * int -> int) ((seq1,tm1),(seq2,tm2)) =
  let 
    val l = combine (seq1,seq2)
    val seqo = SOME (mapi exec l) handle Div => NONE | Overflow => NONE
  in
    case seqo of NONE => () | SOME seq => 
    store_seqtm (seq,list_mk_comb (oper,[tm1,tm2]))
  end

fun ternf (oper, exec: int -> int * int * int -> int) 
  ((seq1,tm1),(seq2,tm2),(seq3,tm3)) =
  let 
    val l = map triple_of_list (list_combine [seq1,seq2,seq3])
    val seqo = SOME (mapi exec l) handle Div => NONE | Overflow => NONE
  in
    case seqo of NONE => () | SOME seq => 
    let val tm = 
      if is_var oper andalso string_of_var oper = "ite" 
      then ite_template (tm1,tm2,tm3) 
      else list_mk_comb (oper,[tm1,tm2,tm3])
    in 
      store_seqtm (seq,tm)
    end
  end

(* -------------------------------------------------------------------------
   Initialization and update steps
   ------------------------------------------------------------------------- *)

fun init nullaryl = 
  let val l1 = map swap (map_snd (fn f => mapi f inputl) nullaryl) in  
    mem_glob := [];
    qd := enew (list_compare Int.compare) (map fst l1);
    seld := dnew Int.compare [(1,l1)]
  end


fun app_all_unop depth unaryl =
  let fun g i = dfind i (!seld) handle NotFound => [] in
    app (fn x => app (unf x) (g (depth - 1))) unaryl
  end

fun app_all_binop depth binaryl = 
  let
    val partl1 = numpart 2 (depth - 1)
    fun g i = dfind i (!seld) handle NotFound => []
    fun get_data l = map pair_of_list (cartesian_productl (map g l))
    val partl2 = map get_data partl1
    fun f part = app (fn x => app (binf x) part) binaryl
  in
    app f partl2
  end

fun app_all_ternop depth ternaryl = 
  let
    val partl1 = numpart 3 (depth - 1)
    fun g i = dfind i (!seld) handle NotFound => []
    fun get_data l = map triple_of_list (cartesian_productl (map g l))
    val partl2 = map get_data partl1
    fun f part = app (fn x => app (ternf x) part) ternaryl
  in
    app f partl2
  end
  
(* -------------------------------------------------------------------------
   Bottom-up search
   ------------------------------------------------------------------------- *)
  
fun next (unaryl,binaryl,ternaryl) depth =
  let
    val _ = mem_glob := []
    val _ = app_all_unop depth unaryl
    val _ = app_all_binop depth binaryl
    val _ = app_all_ternop depth ternaryl
    val _ = seld := dadd depth (!mem_glob) (!seld)
    
    val _ = print_endline (its (dlength (!seld)) ^ " " ^ 
      its (length (!mem_glob)) ^ " " ^ its (elength (!qd))) 
  in
    mem_glob := []
  end;
 
fun kolmo (nullaryl,unaryl,binaryl,ternaryl) depth =
  (
  init nullaryl;  
  app (next (unaryl,binaryl,ternaryl)) 
    (List.tabulate (depth - 1, fn x => x + 2));
  map snd (List.concat (map snd (dlist (!seld))))
  ) 
  
  
val total = ref 0

fun next_limit (unaryl,binaryl,ternaryl) limit depth =
  let
    val _ = mem_glob := []
    val _ = app_all_unop depth unaryl
    val _ = app_all_binop depth binaryl
    val _ = app_all_ternop depth ternaryl
    val _ = total := !total + length (!mem_glob)
    val _ = print_endline (its (dlength (!seld)) ^ " " ^ 
      its (length (!mem_glob)) ^ " " ^ its (elength (!qd))) 
  in
    if !total >= limit orelse depth >= 20
    then 
      let val r = map snd (List.concat (map snd (dlist (!seld)))) in
        r @ (map snd (random_subset (limit - (length r)) (!mem_glob)))
      end
    else (seld := dadd depth (!mem_glob) (!seld); 
          next_limit (unaryl,binaryl,ternaryl) limit (depth + 1))
  end  

fun kolmo_limit (nullaryl,unaryl,binaryl,ternaryl) limit =
  let 
    val _ = (total := 0; init nullaryl)
    val r = next_limit (unaryl,binaryl,ternaryl) limit 2 
  in
    mem_glob := []; r
  end



fun collect_id_aux (Ins (id,argl)) = 
  id :: List.concat (map collect_id_aux argl);

fun collect_id_pp (p1,p2) = 
  mk_fast_set Int.compare (collect_id_aux p1 @ collect_id_aux p2);

val smtv = Vector.fromList (
   map (SOME o (fn (x,i) => mk_var (x, rpt_fun_type (i+1) alpha)))
    [("0",0),("1",0),("2",0),
     ("+",2),("-",2),("*",2),("divf",2),("modf",2),
   ("ite",3)] @ 
   [NONE] @
   map (SOME o (fn x => mk_var (x, alpha))) ["x","y"] @ 
   [NONE,NONE]);

fun kolmo_pp pp limit =
  let 
    val recfl = get_recfl_ws (progpair_to_progxpair_shared pp)
    val idl = collect_id_pp pp;
    val keep = List.mapPartial (fn x => Vector.sub (smtv,x)) idl;
    fun mk_f oper = let fun f i x = random_int (~5,9) in (oper,f) end
    val nullaryf = map mk_f (filter (fn x => arity_of x = 0) recfl)
    val unaryf = map mk_f (filter (fn x => arity_of x = 1) recfl)
    val binaryf = map mk_f (filter (fn x => arity_of x = 2) recfl)
    val ternaryf = map mk_f (filter (fn x => arity_of x = 3) recfl)
    val nullaryl = filter (fn x => tmem (fst x) keep) nullaryl_glob @ nullaryf;
    val unaryl = filter (fn x => tmem (fst x) keep) [] @ unaryf;
    val binaryl = filter (fn x => tmem (fst x) keep) binaryl_glob @ binaryf;
    val ternaryl = filter (fn x => tmem (fst x) keep) ternaryl_glob @ ternaryf;  
  in
    kolmo_limit (nullaryl,unaryl,binaryl,ternaryl) limit
  end
    
end

(*
load "kolmo";
open aiLib kernel smt_hol progx smt_progx kolmo;
val appl = read_anumprogpairs (selfdir ^ "/smt_benchmark_progpairs_sem");
val (a,pp) = random_elem appl;
val tml = kolmo_pp pp 20000;
*)


