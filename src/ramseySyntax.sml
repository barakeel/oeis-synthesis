structure ramseySyntax :> ramseySyntax =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty rconfig
val ERR = mk_HOL_ERR "ramseySyntax"

fun debug_mat m = if !debug_flag then graph.print_mat m else ()

(* -------------------------------------------------------------------------
   Order in which the vertices should be colored
   ------------------------------------------------------------------------- *)

fun pairbelowy y = List.tabulate (y,fn x => (x,y))
fun search_order_undirected size = 
  List.concat (List.tabulate (size,fn y => pairbelowy y))

(* -------------------------------------------------------------------------
   Conversion between edges and variables
   ------------------------------------------------------------------------- *)

val vartoedgev = Vector.fromList (search_order_undirected 50);
fun var_to_edge x = Vector.sub (vartoedgev,x) 
  (* handle Subscript => raise ERR "var_to_edge" (its x) *)
fun edge_to_var (x,y) = 
  if x < y then x + ((y * (y - 1)) div 2) else 
  raise ERR "edge_to_var" (its x ^ "-" ^ its y)

(* -------------------------------------------------------------------------
   Syntax
   ------------------------------------------------------------------------- *)

val E = mk_var ("E",``:num -> num -> bool``)
fun X i = mk_var ("x" ^ its i,``:num``)
fun Xnum x = (string_to_int o tl_string o fst o dest_var) x
fun hvarij (i,j) = list_mk_comb (E,[X i,X j]);
fun hvar v = hvarij (var_to_edge v)
fun is_lit tm = 
  let val tm' = if is_neg tm then dest_neg tm else tm in
    term_eq (fst (strip_comb tm')) E 
  end
  
fun hlit (v,c) = 
  if c = 1 then hvar v else 
  if c = 2 then mk_neg (hvar v) 
  else raise ERR "hlit" "" ;

fun hlit_to_edge tm = 
  let 
    val tm' = if is_neg tm then dest_neg tm else tm
    val (_,argl) = strip_comb tm'
  in
    pair_of_list (map Xnum argl)
  end
  handle HOL_ERR e => (print_endline (term_to_string tm); raise HOL_ERR e)

fun hlit_to_var tm = edge_to_var (hlit_to_edge tm)
  handle HOL_ERR _ => raise ERR "hlit_to_var" ""
fun hlit_to_vc tm = (hlit_to_var tm, if is_neg tm then red else blue)
 
val domain_cache = ref (dempty Int.compare)

fun mk_domain_aux size =
  let
    val vl = List.tabulate (size,X)
    fun f v = numSyntax.mk_less (v,numSyntax.term_of_int size)
    val boundl = map f vl
    val pairvl = map pair_of_list (kernel.subsets_of_size 2 vl)
    val diffl = map (fn (a,b) => mk_neg (mk_eq (a,b))) pairvl
  in
    (vl, list_mk_imp (boundl @ diffl,F))
  end
  
fun mk_domain size =
  dfind size (!domain_cache) handle NotFound => 
  let val r = mk_domain_aux size in
    domain_cache := dadd size r (!domain_cache); r
  end

(* need to be full graph *)
fun term_of_graph graph = 
  let 
    val size = mat_size graph 
    val (vl,domain) = mk_domain size
    val edgecl = mat_to_edgecl graph
    val litl = map hlit (map_fst edge_to_var edgecl)
  in
    list_mk_forall (vl, list_mk_imp (litl,domain)) 
  end

fun mk_domain_only cliquen size =
  let
    val vl = List.tabulate (cliquen,X)
    fun f v = numSyntax.mk_less (v,numSyntax.term_of_int size)
    val boundl = map f vl
    val pairvl = map pair_of_list (kernel.subsets_of_size 2 vl)
    val diffl = map (fn (a,b) => mk_neg (mk_eq (a,b))) pairvl
  in
    list_mk_imp (boundl @ diffl,F)
  end

fun noclique size (cliquen,b) = 
  let
    val vl = List.tabulate (cliquen,X)
    val domain = mk_domain_only cliquen size
    val pairvl = map pair_of_list (subsets_of_size 2 vl)
    val litl = map (fn (a,b) => list_mk_comb (E,[a,b])) pairvl
    val litl' = map (fn x => if b then x else mk_neg x) litl
  in
    list_mk_forall (vl, list_mk_imp (litl',domain)) 
  end
  
fun term_of_edgecl size edgecl =   
  let 
    val edgecl' = filter (fn (_,c) => c <> 0) edgecl 
    val (vl,domain) = mk_domain size
    val litl = map hlit (map_fst edge_to_var edgecl')
  in
    list_mk_forall (vl, list_mk_imp (litl,domain)) 
  end
  

end (* struct *)

(*
load "ramseySyntax"; open ramseySyntax;
val tm1 = noclique 6 (3,true);
val tm2 = noclique 6 (3,false);
*)
