structure match :> match =
struct

open aiLib kernel exec_memo check search

val ERR = mk_HOL_ERR "match"

type seq = kernel.seq
type prog = kernel.prog

(* -------------------------------------------------------------------------
   Enumerate quotiented back functions
   ------------------------------------------------------------------------- *) 

fun enum_backp t = 
  let 
    val _ = backv_glob := backv_default
    val memo = !randsearch_flag
    val _ = randsearch_flag := true
    val _ = movel_glob := filter (fn x => not (mem x [14,15])) movel_default
    val _ = checkinit_matchback ()
    val _ = search (0,t)
    val _ = randsearch_flag := memo
    val seqpl = checkfinal_matchback ();
    val pl = map snd seqpl
  in
    filter (fn p => depend_on_x p andalso contain_id 16 p) pl
  end

(* -------------------------------------------------------------------------
   Tools for computing the intermediate sequence
   ------------------------------------------------------------------------- *) 

(* if too slow, add a cache to f *)
fun back_image backd (p,f) seq = 
  let val lo = map_total f seq in
    case lo of NONE => () | SOME l =>
    (
    case dfindo l (!backd) of
      NONE => backd := dadd l p (!backd) 
    | SOME pold => if prog_compare_size (pold,p) = LESS then () else
                   backd := dadd l p (!backd)
    )
  end;

fun back_image_p backd p seq =
  let 
    val _ = if dlength (!backd) mod 100 = 0 then 
      print_endline (its (dlength (!backd)))
      else ()
    val f = eval_option (exec_memo.mk_exec_onev p) 
  in
    back_image backd (p,f) seq
  end;
  
fun back_image_pl seq pl = 
  let val backd = ref (dempty (list_compare IntInf.compare)) in
    app (fn p => back_image_p backd p seq) pl;
    dlist (!backd)
  end

(* -------------------------------------------------------------------------
   Enumerate quotiented repair functions
   ------------------------------------------------------------------------- *)

fun enum_repairp t = 
  let 
    val memo = !randsearch_flag
    val _ = randsearch_flag := true
    val _ = movel_glob := filter (fn x => not (mem x [14,15,16])) movel_default;
    val _ = checkinit_matchback ()
    val _ = search (0,t)
    val _ = randsearch_flag := memo
    val seqpl = checkfinal_matchback ();
    val pl = map snd seqpl
  in
    pl
  end
  
(* -------------------------------------------------------------------------
   Recovering the final sequence
   ------------------------------------------------------------------------- *) 

fun is_repair_elem f (a,b) = case f a of 
    NONE => false 
  | SOME b' => b' = b;

fun add_cache f =
  let 
    val d = ref (dempty IntInf.compare) 
    fun newf x = 
      case dfindo x (!d) of SOME y => y | NONE => 
      let val y = f x in d := dadd x y (!d); y end
  in
    newf
  end

val repair_cache_flag = ref false

fun create_f p = (if !repair_cache_flag then add_cache else I) 
  (eval_option (exec_memo.mk_exec_onev p)) 

fun is_repair_seq (bseq,seq) (p,f) = 
  all (is_repair_elem f) (combine (bseq,seq))

fun find_repair_one (bseq,seq) pfl = 
  List.find (is_repair_seq (bseq,seq)) pfl

fun find_repair bseql repairpl seq =
  let 
    val pl = dict_sort prog_compare_size repairpl
    val pfl = map_assoc create_f pl
    fun f bseq = case find_repair_one (bseq,seq) pfl of 
      NONE => NONE
    | SOME (p,f) => SOME (bseq,p)
  in
    List.mapPartial f bseql
  end;
 
(* -------------------------------------------------------------------------
   Find functions that are inverse of each other
   ------------------------------------------------------------------------- *)  

type pf = prog * (IntInf.int -> IntInf.int option)

fun is_inverse_one (p1,f1) (p2,f2) x = 
  case f1 x of NONE => false | SOME y =>
  (
  case f2 y of NONE => false | SOME z => x = z
  );
    
fun is_inverse_seq pf1 pf2 seq = all (is_inverse_one pf1 pf2) seq;  
  
fun is_inverse_seql pf1 pf2 seql = 
  exists (is_inverse_seq pf1 pf2) seql;  

val seqllref = ref []

fun next_seql () = 
  let 
    val _ = if null (!seqllref) 
      then seqllref := mk_batch_full 2 (map snd (shuffle bloom.oseql))
      else ()
    val r = hd (!seqllref)
    val _ = seqllref := tl (!seqllref)
  in
    r
  end;

fun collect_inverse_pp invl pf1 pf2 = 
  if is_inverse_seql pf1 pf2 (next_seql ())
  then invl := (pf1,pf2) :: (!invl)
  else ();

fun collect_inverse pfl1 pfl2 =
  let 
    val invl = ref []
    fun f x = 
      let fun g y = collect_inverse_pp invl x y in
        (print "."; app g pfl2)
      end
  in
    app f pfl1;
    !invl
  end;

(* -------------------------------------------------------------------------
   Apply inverse functions to a sequence
   ------------------------------------------------------------------------- *) 
   
fun inverse_elem ((p1,f1):pf,(p2,f2):pf) x = 
  case f1 x of NONE => NONE | SOME y =>
  (
  case f2 y of NONE => NONE | SOME z => if x = z then SOME y else NONE
  );   

fun square x = x*x  
fun size_of_pp (p1,p2) = square (prog_size p1) + square (prog_size p2)

fun update_dglob d newseq (p1:prog,p2:prog) = 
  case dfindo newseq (!d) of 
    NONE => d := dadd newseq (p1,p2) (!d)
  | SOME (oldp1,oldp2) => 
    (
    if triple_compare Int.compare prog_compare_size prog_compare_size
       ((size_of_pp (p1,p2),p1,p2),(size_of_pp (oldp1,oldp2),oldp1,oldp2))
       = LESS
    then d := dadd newseq (p1,p2) (!d)
    else ()
    );

fun inverse_seq d (an,seq) ((p1,f1):pf,(p2,f2):pf) =   
  case map_total (inverse_elem ((p1,f1),(p2,f2))) seq of 
    NONE => ()
  | SOME newseq => update_dglob d newseq (p1:prog,p2:prog)

fun inverse_an pfpfl (an,seq) = 
  let 
    val d = ref (dempty (list_compare IntInf.compare))
    val _ = app (inverse_seq d (an,seq)) pfpfl
    val l = map (fn (a,b) => (a,(an,b))) (dlist (!d))
  in
    l
  end

(* -------------------------------------------------------------------------
   I/O for program pairs with inverse sequence
   ------------------------------------------------------------------------- *) 

fun string_of_inv (seq,(an,(p1,p2))) =
  String.concatWith " | " 
  [string_of_seq seq, its an, gpt_of_prog p1, gpt_of_prog p2]; 

fun write_invl file invl = writel file (map string_of_inv invl)

fun inv_of_string s =
  let 
    val (s1,s2,s3,s4) = 
      quadruple_of_list (String.tokens (fn x => x = #"|") s) 
  in
    (seq_of_string s1, (string_to_int s2, (prog_of_gpt s3, prog_of_gpt s4)))
  end;

fun read_invl file = map inv_of_string (readl file);      

fun inverse_an_unit pfpfl (an,seq) = 
  write_invl (selfdir ^ "/inv/seq/" ^ its an) (inverse_an pfpfl (an,seq));
 
fun human_of_inv (seq,(an,(p1,p2))) =
  String.concatWith " | " 
  [string_of_seq seq, its an, human.humanf p1, human.humanf p2] 
    
(* -------------------------------------------------------------------------
   I/O for program pairs
   ------------------------------------------------------------------------- *) 

fun string_of_pp (p1,p2) = gpt_of_prog p1 ^ " | " ^ gpt_of_prog p2;

fun write_pfpfl file pfpfl = 
  let val ppl = map (fn (a,b) => (fst a, fst b)) pfpfl in
    writel file (map string_of_pp ppl)
  end
  
fun pp_of_string s = 
  let val (s1,s2) = pair_of_list (String.tokens (fn x => x = #"|") s) in
    (prog_of_gpt s1, prog_of_gpt s2)
  end;

fun read_pfpfl file = 
  let 
    val ppl = map pp_of_string (readl file)
    val pfpfl = map (fn (a,b) => ((a, create_f a), (b, create_f b))) ppl
  in
    pfpfl
  end;


end (* struct *)

(* replace memo_flag true by matchback_flag true 

load "match"; open aiLib kernel match;
val repairpl = enum_repairp 10.0; 
val pfl = map_assoc create_f repairpl; 
val (pfpfl,t1) = add_time (collect_inverse pfl) pfl;
write_pfpfl (selfdir ^ "/inv/ppl") pfpfl;


val pfpfl = read_pfpfl (selfdir ^ "/inv/ppl");
fun f (an,seq) = (print "."; (inverse_an_unit pfpfl) (an,seq));
val (_,t) = add_time (app f) bloom.oseql;
  
val invl = read_invl (selfdir ^ "/inv/" ^ its an);
app print_endline (map human_of_inv invl);


*)












  









