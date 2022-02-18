structure tptp :> tptp =
struct 

open HolKernel Abbrev boolLib aiLib
val ERR = mk_HOL_ERR "tptp"

(* -------------------------------------------------------------------------
   Value statements
   ------------------------------------------------------------------------- *)

(* variables *)
val lmc = list_mk_comb;
val alpha3 = rpt_fun_type 3 alpha;
val alpha4 = rpt_fun_type 4 alpha;
val vx = mk_var ("Vx",alpha);
val vy = mk_var ("Vy",alpha);
val vz = mk_var ("Vz",alpha);

(* constants *)
val zero = mk_var ("z",alpha);
val suc = mk_var ("s", rpt_fun_type 2 alpha);
fun mk_suc x = mk_comb (suc,x);

(* First-order axioms *)
(* addition *)
val addi = mk_var ("addi",alpha3);
fun mk_addi (a,b) = lmc (addi,[a,b]);

val ax0 = mk_eq (mk_addi (vx,zero), vx);
val ax1 = mk_eq (mk_addi (vx, mk_suc vy), mk_suc (mk_addi (vx,vy)));

(* substraction *)
val diff = mk_var ("diff",alpha3);
fun mk_diff (a,b) = lmc (diff,[a,b]);
val ax2 = mk_eq (mk_diff (vx, zero), vx);
val ax3 = mk_eq (mk_diff (zero, vx), zero);
val ax4 = mk_eq (mk_diff (mk_suc vx, mk_suc vy),
                 mk_diff (vx,vy));

(* multiplication *)
val mult = mk_var ("mult",alpha3);
fun mk_mult (a,b) = lmc (mult,[a,b]);
val ax5 = mk_eq (mk_mult (vx, zero), zero);
val ax6 = mk_eq (mk_mult (vx, mk_suc vy), 
                 mk_addi (vx, mk_mult (vx,vy)));

(* division *)
val divi = mk_var ("divi",alpha3);
fun mk_divi (a,b) = lmc (divi,[a,b]);

val ax7 = mk_eq (mk_divi (vx, zero), zero);
val sxmy0 = mk_eq (mk_diff (mk_suc vx,vy),zero); (* x < y *)
val ymx0 = mk_eq (mk_diff (vy,vx),zero); (* x >= y *)
val eysz = mk_eq (vy,mk_suc vz); (* y = suc z *)

val ax8 = mk_imp (sxmy0, mk_imp (eysz, 
  mk_eq (mk_divi (vx,vy),zero)));
val ax9 = mk_imp (ymx0,mk_imp (eysz, 
  mk_eq (mk_divi (vx,vy), mk_suc (mk_divi (mk_diff (vx,vy),vy)))));

(*
x div 0 = 0
x < y & y = suc z ==> x div y = 0 
x >= y & y = suc z ==> x div y = suc ((x - y) div y)
*)

(* modulo *)
val modu = mk_var ("modu",alpha3);
fun mk_modu (a,b) = lmc (modu,[a,b]);

val ax10 = mk_eq (mk_modu (vx, zero), zero);
val ax11 = mk_imp (sxmy0, mk_imp (eysz, mk_eq (mk_modu (vx,vy),vx)));
val ax12 = mk_imp (ymx0,mk_imp (eysz, 
  mk_eq (mk_modu (vx,vy), mk_modu (mk_diff (vx,vy),vy))
));


(*
x mod 0 = 0
x < y & y = suc z ==> x mod y = x
x >= y & y = suc z ==> x mod y = (x - y) mod y
e(a+b,0) = e(a,0) + e(b,0)
*)

(* -------------------------------------------------------------------------
   Program statements and evaluation
   ------------------------------------------------------------------------- *)

val va = mk_var ("Va",alpha);
val vb = mk_var ("Vb",alpha);
val vc = mk_var ("Vc",alpha);

(* Evaluation (higher-order) *)
val eval = mk_var ("e", alpha3);
fun mk_eval (a,b) = lmc (eval,[a,b]);

val zerop = mk_var ("zerop",alpha);
val onep = mk_var ("onep",alpha);
val twop = mk_var ("twop",alpha);
val addip = mk_var ("addip", alpha3);
val diffp = mk_var ("diffp", alpha3);
val multp = mk_var ("multp", alpha3);
val divip = mk_var ("divip", alpha3);
val modup = mk_var ("modup", alpha3);
val varp = mk_var ("varp", alpha);

val ax14 = mk_eq (lmc (eval, [zerop,vx]), zero);
val ax15 = mk_eq (lmc (eval, [onep,vx]), mk_comb (suc,zero));
val ax16 = mk_eq (lmc (eval, [twop,vx]), mk_comb (suc,mk_comb (suc,zero)));

fun transfer (operp,oper) = 
  mk_eq ( 
    mk_eval (lmc (operp,[va,vb]),vx), 
    lmc (oper, [mk_eval (va,vx),mk_eval(vb,vx)])
    );

val ax17 = transfer (addip,addi);
val ax18 = transfer (diffp,diff);
val ax19 = transfer (multp,mult);
val ax20 = transfer (divip,divi);
val ax21 = transfer (modup,modu);
val ax22 = mk_eq (lmc (eval, [varp,vx]), vx);

val condp = mk_var ("condp",alpha4);
val cond = mk_var ("cond",rpt_fun_type 5 alpha);

val ax23 = mk_eq (
  mk_eval (lmc (condp, [va,vb,vc]),vx),
  lmc (cond, [mk_eval (va,vx),vb,vc,vx]));
  
val ax24 = mk_eq (lmc (cond, [zero,vb,vc,vx]),mk_eval (vb,vx));
val ax25 = mk_eq (lmc (cond, [mk_suc vy,vb,vc,vx]),mk_eval (vc,vx));

(*
e (condp (a,b,c),x) = cond (e(a,x),b,c,x)
   cond (0,b,c,x) = e(b,x)
   cond (s n,b,c,x) = e(c,x)
*)

val funpowp = mk_var ("funpowp",alpha4);
val funpow = mk_var ("funpow",alpha4);

val ax26 = 
  mk_eq (
    mk_eval (lmc (funpowp, [va,vb,vc]),vx),
    lmc (funpow, [va,mk_eval (vb,vx),mk_eval (vc,vx)]));
  
val ax27 = mk_eq (lmc (funpow, [va,zero,vx]),vx);
val ax28 = mk_eq (lmc (funpow, [va,mk_suc vy,vx]),
  lmc (funpow, [va,vy,mk_eval (va,vx)]));

val axl_prev = [ax0,ax1,ax2,ax3,ax4,ax5,ax6,ax7,ax8,ax9,ax10,ax11,ax12]
       @  [ax14,ax15,ax16,ax17,ax18,ax19,ax20,ax21,ax22,ax23,ax24,ax25,
           ax26,ax27,ax28]

val varl = [vx,vy,vz,va,vb,vc]

fun smart_forall tm = 
  let val vl = filter (fn x => tmem x varl) (free_vars_lr tm) in
    list_mk_forall (vl,tm)
  end

val axl = map smart_forall axl_prev

(*
e (funpowp (a,b,c),x) = funpowp (a,e(b,x),e(c,x))
funpow (a,0,x) = x
funpow (a,suc y,x) = funpow_aux (a,y,e(a,x))
*)

(* -------------------------------------------------------------------------
   Export conjecture from list of numbers
   ------------------------------------------------------------------------- *)

(*
?a. e(a,0) = 0 /\ e(a,1) = 2 ...
*)

fun mk_sucn n = if n <= 0 then zero else mk_suc (mk_sucn (n-1))

fun mk_cj seq = 
  let 
    val seqi = number_fst 0 seq
    fun f(x,y) = mk_eq (mk_eval (va,mk_sucn x), mk_sucn y)
  in
    mk_exists (va, list_mk_conj (map f seqi))
  end


end

(* 
load "tptp"; open tptp; 
load "hhExportFof"; open hhExportFof;

val seq = List.tabulate (16,fn x => x + 1);
p_flag := false;
type_flag := false;
name_flag := false;
fof_export_goal "tptp/atp_in" (axl,mk_cj seq);
*)

