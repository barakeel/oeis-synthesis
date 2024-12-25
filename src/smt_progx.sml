structure smt_progx :> smt_progx =
struct

open HolKernel Abbrev boolLib aiLib dir kernel sexp progx smt_hol
val ERR = mk_HOL_ERR "smt_progx"

type finfo = string * int * bool
type prog = kernel.prog
type progx = progx.progx
type sexp = sexp.sexp

(* --------------------------------------------------------------------------
   HOL terms to program
   -------------------------------------------------------------------------- *)

fun find_allfun vls deftop = 
  let
    val acc = ref []
    val reserved = (["0","1","2","+","-","*","divf","modf","<=","ite"] @ vls)
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

fun hol_to_progx_aux fd def =
  let 
    fun fop s argl = 
      Insx ((oper_of_name s,NONE), map (hol_to_progx_aux fd) argl)
    val (oper,argl) = strip_comb def
  in
    case string_of_var oper of
      "0" => fop "zero" argl
    | "1" => fop "one" argl
    | "2" => fop "two" argl
    | "+" => fop "addi" argl
    | "-" => fop "diff" argl
    | "*" => fop "mult" argl
    | "divf" => fop "divi" argl
    | "modf" => fop "modu" argl
    | "ite" =>
      let 
        val (a,b,c) = triple_of_list argl 
        val (a',_) = pair_of_list (snd (strip_comb a)) 
      in
        fop "cond" [a',b,c]
      end
    | "x" => fop "x" argl
    | "y" => fop "y" argl 
    | s => dfind s (!fd)        
  end;

fun hol_to_progx operd (memd,fd) tm = 
  let
    val (decl,def) = dest_eq (snd (strip_forall tm)) 
    val opers = string_of_var (fst (strip_comb decl))
    val vls = map string_of_var (snd (strip_comb decl))
    val operc = hd_string opers
    val operi = tl_string opers
    val (ts,us,vs,ws) = ("t" ^ operi,"u" ^ operi,"v" ^ operi,"w" ^ operi)
    fun memorize () = 
      let 
        val recsl = find_allfun vls def
        val recs = singleton_of_list 
          (filter (fn x => not (mem (hd_string x) [#"t",#"u",#"v"])) recsl)
          handle HOL_ERR _ => raise ERR "hol_to_progx" 
            (String.concatWith " " recsl)
       in
         memd := dadd opers recs (!memd)
       end
    fun f_ho honame hoargl =
       let
         val a = (oper_of_name honame, SOME opers)
         val hoprogxl = map (fn x => dfind (dfind x (!memd)) (!fd)) hoargl
         val (_,argl) = strip_comb def 
         val progxl = map (hol_to_progx_aux fd) argl
         val r = Insx (a, hoprogxl @ progxl)
      in
        fd := dadd opers r (!fd)
      end 
  in
    (* compr *)
    if operc = #"t" then memorize ()
    else if operc = #"u" andalso emem ts operd then ()
    else if operc = #"v" andalso emem ts operd then f_ho "compr" [ts] 
    (* loop *)
    else if operc = #"u" andalso emem vs operd andalso not (emem ws operd) 
      then memorize ()
    else if operc = #"v" andalso not (emem ws operd) then f_ho "loop" [us]
    (* loop2 *)   
    else if mem operc [#"u",#"v"] andalso emem ws operd then memorize ()
    else if operc = #"w" then f_ho "loop2" [us,vs]
    (* other *)
    else fd := dadd opers (hol_to_progx_aux fd def) (!fd)
  end

fun hol_to_progxpair idtml = 
  let 
    val (idl,tml) = split idtml
    val operd = enew String.compare (map #1 idl)
    val memd = ref (dempty String.compare)
    val fd = ref (dempty String.compare)
  in
    app (hol_to_progx operd (memd,fd)) tml; 
    (dfind "small" (!fd), dfind "fast" (!fd))
  end

fun read_smt_progxpair file = 
  hol_to_progxpair (read_smt_hol (selfdir ^ "/smt/" ^ file))

fun read_smt_progpair file = 
  progxpair_to_progpair (read_smt_progxpair file)

(* --------------------------------------------------------------------------
   Reading and writing list of program pairs to a single file
   -------------------------------------------------------------------------- *)
   
fun write_anumprogpairs file appl = 
  let
    fun f (s,(p1,p2)) = String.concatWith " | "
      [OS.Path.base s, gpt_of_prog p1, gpt_of_prog p2]
    fun mycmp (s1,s2) = 
      Int.compare (string_to_int (tl_string s1), string_to_int (tl_string s2))
    val l = map f (dict_sort (fst_compare mycmp) appl)
  in
    writel file l
  end
  
fun read_anumprogpairs file = 
  let 
    fun f s = 
      let val (a,b,c) = triple_of_list (String.tokens (fn x => x = #"|") s) in
        (singleton_of_list (String.tokens Char.isSpace a), 
         (prog_of_gpt b, prog_of_gpt c))
      end
  in
    map f (readl file)
  end
  
(*
load "smt_progx"; open aiLib kernel smt_progx;
val filel = listDir (selfdir ^ "/smt");
val appl = map_assoc read_smt_progpair filel;
write_anumprogpairs "smt_benchmark_progpairs" appl;
val newappl = read_anumprogpairs "smt_benchmark_progpairs";

 fun mycmp (s1,s2) = 
      Int.compare (string_to_int (tl_string s1), string_to_int (tl_string s2));
map snd (dict_sort (fst_compare mycmp) appl) = map snd newappl;

*)  

(* --------------------------------------------------------------------------
   Helping functions for constructing HOL terms
   -------------------------------------------------------------------------- *)

fun mk_varn (n,k) = mk_var (n, rpt_fun_type (k+1) alpha) 
fun auto_comb (n,tml) = list_mk_comb (mk_varn (n,length tml),tml)

val smtnamev = Vector.fromList
  ["0","1","2","+","-","*","divf","modf",
   "ite","loop_none","x","y","compr_none","loop2_none"]
   
fun smtname id = Vector.sub (smtnamev,id)

fun arity_of_progx px =     
  let 
    val p = progx_to_prog px 
    val arity = if depend_on_y p then 2 else if depend_on_x p then 1 else 0
  in
    arity
  end

fun varl_of_progx px =     
  let 
    val p = progx_to_prog px 
    val arity = 
      if depend_on_y p then [mk_var ("x",alpha), mk_var ("y",alpha)] 
      else if depend_on_x p then [mk_var ("x",alpha)] 
      else []
  in
    arity
  end
  
fun namea_of_px (px as (Insx ((_, vo),_))) = (valOf vo, arity_of_progx px);

fun get_recfl (px1,px2) = 
  let 
    fun mycmp (s1,s2) = Int.compare 
      (string_to_int (tl_string s1),string_to_int (tl_string s2));
    val sl = mk_fast_set (cpl_compare String.compare Int.compare) 
      (map namea_of_px ((all_subnamed px1) @ (all_subnamed px2)))
  in
    map mk_varn (dict_sort (cpl_compare mycmp Int.compare) sl)
  end; 

fun namep_of_px (px as (Insx ((_, vo),_))) = 
  ((valOf vo, arity_of_progx px), progx_to_prog px);

fun get_recfpl (px1,px2) =
  let 
    fun mycmp (s1,s2) = Int.compare 
      (string_to_int (tl_string s1), string_to_int (tl_string s2))
    val l = mk_fast_set (fst_compare (fst_compare mycmp))
      (map namep_of_px ((all_subnamed px1) @ (all_subnamed px2)))   
  in
    map_fst mk_varn l
  end;  

(* --------------------------------------------------------------------------
   Adding SMT definition for loop2_snd
   -------------------------------------------------------------------------- *)

fun mk_svar tm = mk_varn ("s" ^ tl_string (string_of_var tm), arity_of tm)
 
fun add_s tm = 
  if hd_string (string_of_var tm) = #"w" 
  then [tm, mk_svar tm]
  else [tm]; 
 
fun get_recfl_ws (px1,px2) = List.concat (map add_s (get_recfl (px1,px2)))

fun add_sp (tm,(p as Ins (_,pl))) = 
  if hd_string (string_of_var tm) = #"w"
  then [(tm,p), (mk_svar tm, Ins (16,pl))]
  else [(tm,p)]

fun get_recfpl_ws (px1,px2) = List.concat (map add_sp (get_recfpl (px1,px2)))

fun add_sdec tm =
  let 
    val (orgvl,body) = strip_forall tm
    val (a,b) = dest_eq body
    val (operu,argl) = strip_comb b
    val (oper,vl) = strip_comb a
    val is = tl_string (string_of_var oper)
  in
    if hd_string (string_of_var oper) <> #"w" then [tm] else 
    let 
      val stm = auto_comb ("s" ^ is, vl)
      val vtm = auto_comb ("v" ^ is, argl)
    in
      [tm, list_mk_forall (orgvl, mk_eq (stm,vtm))]  
    end    
  end;
  
fun add_sdecl tml = List.concat (map add_sdec tml)
    

(* --------------------------------------------------------------------------
   Templates for auxilliary functions of loops
   -------------------------------------------------------------------------- *)

val xvar = mk_var ("x",alpha)
val yvar = mk_var ("y",alpha)
val zvar = mk_var ("z",alpha)
val var0 = mk_varn("0",0);
val var1 = mk_varn("1",0);
val xvari = auto_comb ("+",[xvar,var1]);
val xvard = auto_comb ("-",[xvar,var1]);
val yvari = auto_comb ("+",[yvar,var1]);
val yvard = auto_comb ("-",[yvar,var1]);
val zvari = auto_comb ("+",[zvar,var1]);
val zvard = auto_comb ("-",[zvar,var1]);

fun ite_template t1 t2 t3 =
  auto_comb ("ite", [auto_comb ("<=", [t1,var0]),t2,t3]);

fun loop_template us fs farity = 
  let 
    val rcall = auto_comb (us,[xvard,yvar])
    val argl = [rcall,xvar]
    val updtm = auto_comb (fs, first_n farity argl)
    val itetm = ite_template xvar yvar updtm
    val eqtm = mk_eq (auto_comb (us,[xvar,yvar]),itetm)
  in
    [list_mk_forall ([xvar,yvar],eqtm)]
  end;
  
fun compr_template_t ts fs farity = 
  let
    val argl = [xvar,var0]
    val updtm = auto_comb (ts,[xvari])
    val condtm = auto_comb (fs, first_n farity argl)
    val itetm = ite_template condtm xvar updtm
    val eqtm = mk_eq (auto_comb (ts,[xvar]),itetm)
  in
    list_mk_forall ([xvar],eqtm)
  end;
  
fun compr_template_u us ts = 
  let
    val basetm = auto_comb (ts,[var0])
    val updtm = auto_comb (ts,[auto_comb ("+",[auto_comb (us,[xvard]),var1])])
    val itetm = ite_template xvar basetm updtm
    val eqtm = mk_eq (auto_comb (us,[xvar]),itetm)
  in
    list_mk_forall ([xvar],eqtm)
  end;  

fun compr_template us ts fs farity = 
  [compr_template_t ts fs farity, compr_template_u us ts];

fun loop2_template_u us vs fs farity =
  let
    val argl = [auto_comb (us,[xvard,yvar,zvar]),
                auto_comb (vs,[xvard,yvar,zvar])]
    val updtm = auto_comb (fs, first_n farity argl)
    val itetm = ite_template xvar yvar updtm
    val eqtm = mk_eq (auto_comb (us,[xvar,yvar,zvar]),itetm)
  in
    list_mk_forall ([xvar,yvar,zvar],eqtm)
  end
  
fun loop2_template_v us vs gs garity =
  let
    val argl = [auto_comb (us,[xvard,yvar,zvar]),
                auto_comb (vs,[xvard,yvar,zvar])]
    val updtm = auto_comb (gs, first_n garity argl)
    val itetm = ite_template xvar zvar updtm
    val eqtm = mk_eq (auto_comb (vs,[xvar,yvar,zvar]),itetm)
  in
    list_mk_forall ([xvar,yvar,zvar],eqtm)
  end  

fun loop2_template us vs fs gs farity garity = 
  [loop2_template_u us vs fs farity,
   loop2_template_v us vs gs garity]


(* --------------------------------------------------------------------------
   Helper equations (could do loop equations too)
   -------------------------------------------------------------------------- *)

fun eq_loop (px1,px2) =
  let 
    val (pxl1,pxl2) = (all_subloop px1, all_subloop px2) 
    val pxl3 = pxl1 @ pxl2  
    val d = dappendl (map hoarg_loop pxl3) (dempty progx_compare)
    val vl = [xvar,yvar]
    fun g (s1,s2) = list_mk_forall (vl, 
      mk_eq (auto_comb ("u" ^ s1, vl), auto_comb ("u" ^ s2, vl)))
    fun f (p,sl) = if length sl <= 1 then [] else map g (all_pairs sl)
  in
    List.concat (map f (dlist d))
  end
  
fun eq_loop_imp (px1,px2) =
  let 
    val pxl = mk_fast_set progx_compare (all_subloop px1 @ all_subloop px2)   
    val hhl = all_pairs (map hoarg_loop pxl)
    fun g ((px1,s1),(px2,s2)) =
      let
        val vl = [xvar,yvar] 
        val arity1 = arity_of_progx px1
        val arity2 = arity_of_progx px2
        val vlaux = first_n (Int.max (arity1,arity2)) vl
        val ante = list_mk_forall (vlaux,
          mk_eq (auto_comb ("f" ^ s1, first_n arity1 vl), 
                 auto_comb ("f" ^ s2, first_n arity2 vl)))
        val concl = list_mk_forall (vl, 
          mk_eq (auto_comb ("u" ^ s1, vl), auto_comb ("u" ^ s2, vl)))
      in
        mk_imp (ante,concl) 
      end
  in
    map g hhl
  end

fun eq_compr (px1,px2) =
  let 
    val (pxl1,pxl2) = (all_subcompr px1, all_subcompr px2) 
    val pxl3 = pxl1 @ pxl2  
    val d = dappendl (map hoarg_compr pxl3) (dempty progx_compare)
    val vl = [xvar]
    fun g (s1,s2) = 
      list_mk_forall (vl, 
        mk_eq (auto_comb ("u" ^ s1, vl), auto_comb ("u" ^ s2, vl)))
    fun f (p,sl) = 
      if length sl <= 1 then [] else map g (all_pairs sl)
  in
    List.concat (map f (dlist d))
  end
  
fun eq_compr_imp (px1,px2) =
  let 
    val pxl = mk_fast_set progx_compare (all_subcompr px1 @ all_subcompr px2)   
    val hhl = all_pairs (map hoarg_compr pxl)
    fun g ((px1,s1),(px2,s2)) =
      let
        val vl = [xvar,yvar] 
        val arity1 = arity_of_progx px1
        val arity2 = arity_of_progx px2
        val vlaux = first_n (Int.max (arity1,arity2)) vl
        val ante = list_mk_forall (vlaux,
          mk_eq (auto_comb ("f" ^ s1, first_n arity1 vl), 
                 auto_comb ("f" ^ s2, first_n arity2 vl)))
        val concl = list_mk_forall (vl, 
          mk_eq (auto_comb ("u" ^ s1, [xvar]), auto_comb ("u" ^ s2, [xvar])))
      in
        mk_imp (ante,concl) 
      end
  in
    map g hhl
  end  

fun eq_loop2_1 (px1,px2) =
  let 
    val (pxl1,pxl2) = (all_subloop2 px1, all_subloop2 px2) 
    val pxl3 = pxl1 @ pxl2  
    val d = dappendl (map hoarg_loop2_1 pxl3) (dempty progx_compare)
    val vl = [xvar,yvar,zvar]
    fun g (s1,s2) = list_mk_forall (vl, 
      mk_eq (auto_comb ("u" ^ s1, vl), auto_comb ("u" ^ s2, vl)))
    fun f (p,sl) = if length sl <= 1 then [] else map g (all_pairs sl)
  in
    List.concat (map f (dlist d))
  end

fun eq_loop2_2 (px1,px2) =
  let 
    val (pxl1,pxl2) = (all_subloop2 px1, all_subloop2 px2) 
    val pxl3 = pxl1 @ pxl2  
    val d = dappendl (map hoarg_loop2_2 pxl3) (dempty progx_compare)
    val vl = [xvar,yvar,zvar]
    fun g (s1,s2) = list_mk_forall (vl, 
      mk_eq (auto_comb ("v" ^ s1, vl), auto_comb ("v" ^ s2, vl)))
    fun f (p,sl) = if length sl <= 1 then [] else map g (all_pairs sl)
  in
    List.concat (map f (dlist d))
  end

fun eq_loop2_imp (px1,px2) =
  let 
    val pxl = mk_fast_set progx_compare (all_subloop2 px1 @ all_subloop2 px2)   
    val hhl = all_pairs (map hoarg_loop2 pxl)
    fun g (((px1,qx1),s1),((px2,qx2),s2)) =
      let
        val vl = [xvar,yvar,zvar] 
        val arity1 = arity_of_progx px1
        val arity2 = arity_of_progx px2
        val arity3 = arity_of_progx qx1
        val arity4 = arity_of_progx qx2
        val vlaux1 = first_n (Int.max (arity1,arity2)) vl
        val ante1 = list_mk_forall (vlaux1,
          mk_eq (auto_comb ("f" ^ s1, first_n arity1 vl), 
                 auto_comb ("f" ^ s2, first_n arity2 vl)))
        val vlaux2 = first_n (Int.max (arity3,arity4)) vl
        val ante2 = list_mk_forall (vlaux2,
          mk_eq (auto_comb ("g" ^ s1, first_n arity3 vl), 
                 auto_comb ("g" ^ s2, first_n arity4 vl)))
        val concl1 = list_mk_forall (vl, 
          mk_eq (auto_comb ("u" ^ s1, vl), auto_comb ("u" ^ s2, vl)))
        val concl2 = list_mk_forall (vl, 
          mk_eq (auto_comb ("v" ^ s1, vl), auto_comb ("v" ^ s2, vl)))
      in
        mk_imp (mk_conj (ante1,ante2), mk_conj (concl1,concl2)) 
      end
  in
    map g hhl
  end

(* --------------------------------------------------------------------------
   Program to HOL terms
   -------------------------------------------------------------------------- *)

fun pxx_to_hol_aux (px as (Insx ((id,no),pl))) = case no of
    NONE => 
    (
    case px of
      Insx ((8,_),[p1,p2,p3]) =>
      let val (a1,a2,a3) = triple_of_list 
        (map pxx_to_hol_aux [p1,p2,p3])                 
      in
        ite_template a1 a2 a3
      end
    | _ =>
      let 
        val argl = map pxx_to_hol_aux pl
        val oper = mk_var (smtname id, rpt_fun_type (length argl + 1) alpha) 
      in
        list_mk_comb (oper,argl)
      end
    )
  | SOME n => auto_comb (hd (String.tokens Char.isSpace n), varl_of_progx px) 
 

fun add_eq nl vl = case nl of
   [n1,n2] =>  
   let val vl' = 
     if mem n1 ["small","fast"] then 
       if length vl >= 2 
       then raise ERR "add_eq" "small-fast: arity 2" 
       else [xvar]
     else vl 
   in 
     [list_mk_forall (vl', mk_eq (auto_comb (n1,vl'), auto_comb (n2,vl)))]
   end
  | _ => []

fun pxx_to_hol (px as (Insx ((id,no),pl))) = case no of
    NONE => raise ERR "pxx_to_hol" "unexpected"
  | SOME nls => 
    let
      val nl = String.tokens Char.isSpace nls
      val _ = if length nl > 2 then raise ERR "pxx_to_hol_aux" "2" else ()
      val nlast = last nl
      val is = tl_string nlast
      val vl = varl_of_progx px
    in
      case px of
        Insx ((9,_),[p1,p2,p3]) =>
        let
          val (us,fs) = ("u" ^ is,"f" ^ is)
          val farity = arity_of_progx p1
          val (a2,a3) = pair_of_list (map pxx_to_hol_aux [p2,p3])
          val eqtm = mk_eq (auto_comb (nlast,vl), auto_comb (us,[a2,a3]))
        in
          loop_template us fs farity @ 
          [list_mk_forall (vl,eqtm)] @
          add_eq nl vl
        end
      | Insx ((12,_),[p1,p2]) =>
        let
          val (us,ts,fs) = ("u" ^ is,"t" ^ is,"f" ^ is)
          val farity = arity_of_progx p1
          val a2 = pxx_to_hol_aux p2
          val eqtm = mk_eq (auto_comb (nlast,vl), auto_comb (us,[a2]))
        in
          compr_template us ts fs farity @
          [list_mk_forall (vl,eqtm)] @
          add_eq nl vl
        end
      | Insx ((13,_),[p1,p2,p3,p4,p5]) => 
        let
          val (us,vs,fs,gs) = ("u" ^ is,"v" ^ is,"f" ^ is,"g" ^ is)
          val farity = arity_of_progx p1
          val garity = arity_of_progx p2
          val (a3,a4,a5) = triple_of_list (map pxx_to_hol_aux [p3,p4,p5])
          val eqtm = mk_eq (auto_comb (nlast,vl), auto_comb (us,[a3,a4,a5]))
        in
          loop2_template us vs fs gs farity garity @
          [list_mk_forall (vl,eqtm)] @
          add_eq nl vl
        end
      | Insx ((16,_),[p1,p2,p3,p4,p5]) => 
        let
          val (us,vs,fs,gs) = ("u" ^ is,"v" ^ is,"f" ^ is,"g" ^ is)
          val farity = arity_of_progx p1
          val garity = arity_of_progx p2
          val (a3,a4,a5) = triple_of_list (map pxx_to_hol_aux [p3,p4,p5])
          val eqtm = mk_eq (auto_comb (nlast,vl), auto_comb (us,[a3,a4,a5]))
        in
          loop2_template us vs fs gs farity garity @
          [list_mk_forall (vl,eqtm)] @
          add_eq nl vl
        end
      | _ => 
       let
         val _ = if length nl > 1 then raise ERR "pxx_to_hol_aux" "1" else ()
         val vl' = 
           if mem nlast ["small","fast"]
           then 
             if arity_of_progx px >= 2 
             then raise ERR "pxx_to_hol" "small-fast: arity 2"
             else [xvar]
           else vl         
         val eqtm = mk_eq (auto_comb (nlast,vl'), 
                           pxx_to_hol_aux (unname_progx px))
       in
         [list_mk_forall (vl',eqtm)]
       end
    end;
 
 
end (* struct *)
