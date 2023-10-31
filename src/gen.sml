(* =========================================================================
   Compute a set of genralized graphs covering a set of graphs
   ========================================================================= *)
   
structure gen :> gen =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty sat rconfig
  rconfig satenc smlParallel
val ERR = mk_HOL_ERR "gen"
type vleafs = int * int * (IntInf.int * int list) list  

val nauty_time = ref 0.0
val normalize_nauty = total_time nauty_time normalize_nauty

(* -------------------------------------------------------------------------
   Getting all_leafs of 
   ------------------------------------------------------------------------- *) 

fun apply_coloring m edgecl = 
   let 
     val newm = mat_copy m
     fun f ((i,j),c) = mat_update_sym (newm,i,j,c) 
   in
     app f edgecl; newm
   end

fun all_coloring edgel = 
  let
    val edgebothl =
      let 
        val l = ref []
        fun f (i,j) = l := [((i,j),blue),((i,j),red)] :: !l 
      in 
        (app f edgel; !l)
      end
  in
    cartesian_productl edgebothl
  end

fun all_leafs_wperm uset m =
  let
    val edgel = all_holes m
    val coloringltop = all_coloring edgel
    val d = ref (dempty IntInf.compare)
    fun loop d e coloringl = case coloringl of 
        [] => (d,e)
      | coloring :: cont =>
        let 
          val child = apply_coloring m coloring     
          val (normm,perm) = normalize_nauty_wperm child
          val normi = zip_mat normm
          val newe = eadd normi e
        in
          if emem normi uset
          then loop (dadd normi perm d) newe cont   
          else loop d newe cont
        end
  in
    loop (dempty IntInf.compare) (eempty IntInf.compare) coloringltop 
  end

(* -------------------------------------------------------------------------
   Cover
   ------------------------------------------------------------------------- *)

fun enc_color (x,c) = if c = 1 then 2 * x else 2 * x + 1;
fun enc_edgec (e,c) = enc_color (edge_to_var e,c);
fun dec_edgec x = (var_to_edge (x div 2), (x mod 2) + 1);
fun opposite (e,x) = (e,3 - x)

fun init_sgen size (bluen,redn) = 
  let
    val clauses1 = sat.ramsey_clauses size (bluen,redn)
    val clauses2 = map (map enc_color) clauses1
    val clausev = Vector.fromList clauses2;
    val claused = dnew (list_compare Int.compare) (number_snd 0 clauses2)
    fun g clause = map_assoc (fn _ => clause) clause
    val clauses3 = List.concat (map g clauses2)
    val clauses4 = dlist (dregroup Int.compare clauses3)
    val clauses5 = map_snd (map (fn x => dfind x claused)) clauses4
    val clauses6 = map_snd (dict_sort Int.compare) clauses5
    val varv = Vector.fromList (map snd clauses6)
  in
    (varv,clausev)
  end;
  
fun build_parent leaf edgel = 
  let
    val parent = mat_copy leaf
    fun f (i,j) = mat_update_sym (parent,i,j,0)
    val _ = app f edgel
  in
    parent
  end;     
  
fun build_sibling leaf edgel (itop,jtop) = 
  let
    val sibling = build_parent leaf edgel
    val oppc = 3 - mat_sub (leaf,itop,jtop)
    val _ = mat_update_sym (sibling,itop,jtop,oppc)
  in
    sibling
  end

fun concat_cpermll (leafi,vleafsl) = 
  let val idperm = List.tabulate (mat_size (unzip_mat leafi),I) in
    mk_fast_set (fst_compare IntInf.compare)
      ((leafi,idperm) :: List.concat (map #3 vleafsl))
  end
  
val threshold = 4 (* percentage of newly covered graph *)

fun sgeneralize (bluen,redn) uset leafi =
  let
    val leaf = unzip_mat leafi
    val size = mat_size leaf
    val (varv,clausev) = init_sgen size (bluen,redn) 
    val sizev = Vector.map (fn x => length x - 1) clausev
    val inita = Array.array (Vector.length clausev,0)    
    fun update_numbera a v = 
      let 
        val il = Vector.sub (varv,v) 
        fun g i = Array.update (a,i, Array.sub(a,i) + 1) 
      in
        app g il
      end
    val edgecl = mat_to_edgecl leaf
    val _ = app (update_numbera inita) (map enc_edgec edgecl)
    fun try () = 
      let
        val locala = Array.tabulate 
          (Array.length inita, fn i => Array.sub (inita,i))
        val vlopp = shuffle (map (enc_edgec o opposite) edgecl)
        fun test v = 
          let val clausel = Vector.sub (varv,v) in
            all (fn x => Array.sub (locala, x) < Vector.sub(sizev,x)) clausel
          end
        fun sgen_loop vl result = case vl of
            [] => rev result
          | v :: rem => 
            let 
              val edgel = map (fst o dec_edgec o #1) result
              val edge = fst (dec_edgec v)
              val sibling = build_sibling leaf edgel edge
              val (d,e) = all_leafs_wperm uset sibling
              val maxn = elength e
            in
              if threshold * dlength d  > maxn
              then (update_numbera locala v; 
                    sgen_loop (filter test rem) ((v,maxn,dlist d) :: result)) 
              else sgen_loop rem result
            end   
      in
        sgen_loop (filter test vlopp) []
      end 
  in  
    try ()
  end;

(* -------------------------------------------------------------------------
   Finding generalizations not overlapping too much
   ------------------------------------------------------------------------- *)
   
fun sgen_worker ((bluen,redn),uset) leafi =
  let
    val vleafsl = sgeneralize (bluen,redn) uset leafi in
    (leafi, vleafsl)
  end

fun write_infset file ((a,b),set) = writel file 
  (its a :: its b :: map infts (elist set))
fun read_infset file = case readl file of
  sa :: sb :: m => ((string_to_int sa,string_to_int sb), 
                    enew IntInf.compare (map stinf m))
  | _ => raise ERR "read_infset" ""
 
fun write_inf file i = writel file [infts i]
fun read_inf file = stinf (singleton_of_list (readl file))

fun string_of_cperm (c,perm) = 
  String.concatWith "_" (infts c :: map its perm)

fun cperm_of_string s = case String.tokens (fn x => x = #"_") s of
    a :: m => (stinf a, map string_to_int m)
  | _ => raise ERR "cperm_of_string" ""

fun string_of_vleafs (v,maxn,cperml) = 
  String.concatWith " " (its v :: its maxn :: map string_of_cperm cperml)

fun vleafs_of_string s = case String.tokens Char.isSpace s of
    a :: b :: m => (string_to_int a, string_to_int b, map cperm_of_string m)
  | _ => raise ERR "vleafs_of_string" ""

fun write_result file (leafi,vleafsl)  =
  writel file (infts leafi :: map string_of_vleafs vleafsl)

fun read_result file = case readl file of 
    a :: m => (stinf a, map vleafs_of_string m)
  | _ => raise ERR "read_result" ""

val genspec : ((int * int) * IntInf.int Redblackset.set, IntInf.int, 
  IntInf.int * vleafs list) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "gen.genspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = sgen_worker,
  write_param = write_infset,
  read_param = read_infset,
  write_arg = write_inf,
  read_arg = read_inf,
  write_result = write_result,
  read_result = read_result
  }

fun remove_vleafsl_aux uset (leafi,vleafsl) acc = case vleafsl of
    [] => SOME (leafi, rev acc)
  | (v,maxn,cperml) :: m =>  
    let val newcperml = filter (fn x => emem (fst x) uset) cperml in
      if threshold * length newcperml > maxn 
      then remove_vleafsl_aux uset (leafi,m) ((v,maxn,newcperml) :: acc)
      else NONE
    end

fun remove_vleafsl uset (leafi,vleafsl) = 
  if not (emem leafi uset) then NONE else 
  remove_vleafsl_aux uset (leafi,vleafsl) []


val select_number1 = ref 240
val select_number2 = ref 120

fun update_uset selectn pl (uset,result) =
  if elength uset <= 0 orelse 
     null pl orelse selectn >= !select_number2 then (uset,result) else
  let 
    val l1 = map_assoc (length o snd) pl
    val l2 = dict_sort compare_imax l1
    val (leafi,vleafsl) = fst (hd l2) 
    val cperml = concat_cpermll (leafi,vleafsl)
    val keyl = map fst cperml
    val newuset = ereml keyl uset
    val edgel = map (fst o dec_edgec o #1) vleafsl
    val pari = zip_mat (build_parent (unzip_mat leafi) edgel)
    val newresult = (pari,cperml) :: result
    val newpl = List.mapPartial (remove_vleafsl newuset) pl
    val _ = log ("Covering " ^ its (length cperml) ^ " graphs (" ^ 
                 its (elength newuset) ^ " remaining)" ^
                 " at depth " ^ its (length vleafsl))
  in
    update_uset (selectn + 1) newpl (newuset,newresult)
  end

fun loop_scover_para ncore (bluen,redn) uset result = 
  if elength uset <= 0 then rev result else
  let
    val n = Int.min (!select_number1, elength uset)
    val ul = random_subset n (elist uset)
    val n' = Int.min (n,ncore)
    val param = ((bluen,redn),uset)
    val _ = clean_dir (selfdir ^ "/parallel_search")
    val pl = smlParallel.parmap_queue_extern n' genspec param ul
    val (newuset,newresult) = update_uset 0 pl (uset,result)
  in
    loop_scover_para ncore (bluen,redn) newuset newresult
  end

fun compute_scover_para ncore size (bluen,redn) = 
  let
    val id = its bluen ^ its redn ^ its size
    val file = selfdir ^ "/ramsey_data/enum" ^ id
    val uset = enew IntInf.compare (map stinf (readl file));
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 12000)
  in
    loop_scover_para ncore (bluen,redn) uset []
  end

fun store_cover size (bluen,redn) cover = 
  let 
    val dir = selfdir ^ "/ramsey_data";
    val file = dir ^ "/gen" ^ its bluen ^ its redn ^ its size
    fun f (p,cperml) = 
      let fun g (c,perm) = infts c ^ "_" ^ 
        String.concatWith "_" (map its perm) 
      in
        String.concatWith " " (infts p :: map g cperml)
      end
  in
    mkDir_err dir;
    writel file (map f cover)
  end  

fun gen ncore (bluen,redn) (minsize,maxsize) =  
  let
    fun f size =
      let
        val _ = print_endline ("SIZE " ^ its size)
        val cover = compute_scover_para ncore size (bluen,redn)
      in
        store_cover size (bluen,redn) cover
      end  
  in
    ignore (range (minsize,maxsize,f))
  end
  
(*
PolyML.print_depth 0;
load "enum"; load "gen"; open sat aiLib kernel graph gen enum;
PolyML.print_depth 10;

clean_dir (selfdir ^ "/ramsey_data");

val ncore = 60;
val (_,t0) = add_time (enum ncore) (3,5);
val (_,t1) = add_time (enum ncore) (4,4);


PolyML.print_depth 0;
load "enum"; load "gen"; open sat aiLib kernel graph gen enum;
PolyML.print_depth 10;
val ncore = 60;
select_number1 := 313;
select_number2 := 1;
val (_,t2) = add_time (gen ncore (3,5)) (5,13);

select_number1 := 1000;
select_number2 := 100;
val (_,t3) = add_time (gen ncore (4,4)) (4,17);
*)

(* -------------------------------------------------------------------------
   Cone generalization
   ------------------------------------------------------------------------- *)

val cone_compare = list_compare Int.compare
val cone_set = mk_fast_set cone_compare   

fun parents cl = case cl of 
    [] => []
  | a :: m => 
      if a <> 0 
      then (0 :: m) :: map (fn x => a :: x) (parents m)
      else map (fn x => a :: x) (parents m)
  
fun instances cl = 
  let val cl' =  map (fn x => if x = 0 then [1,2] else [x]) cl in 
    cartesian_productl cl'
  end
  
fun cnext cset childl = 
  let  
    val childset = enew (list_compare Int.compare) childl
    val l1 = cone_set (List.concat (map parents childl))
    fun is_fullanc m = all (fn x => emem x cset) (instances m)
    val l2 = filter is_fullanc l1
  in
    (* random_subset (!gen_width) *) l2
  end;

fun cloop cset childl =
  let val parentl = cnext cset childl
  in
    if null parentl
    then (random_elem childl)
    else cloop cset parentl
  end;
  
fun cgeneralize cset leaf = cloop cset [leaf];
  
fun n_hole cl = length (filter (fn x => x = 0) cl);  
  
fun ccover_loop uset = 
  if elength uset <= 0 then [] else 
  let 
    val (parentl,t) = add_time (map (cgeneralize uset)) (elist uset)
    val parentlsc = map_assoc n_hole parentl
    val (parent,sc) = hd (dict_sort compare_imax parentlsc)
    val leafs = instances parent
    val newuset = ereml leafs uset
    val _ = log (its (elength newuset) ^ " " ^ rts_round 2 t)
  in
    parent :: ccover_loop newuset
  end
      
fun ccover conel = ccover_loop (enew cone_compare conel)

(*
load "gen"; open gen sat;

(* creating all cones *)
PolyML.print_depth 0;
load "ramsey"; load "gen"; load "sat"; 
open ramsey aiLib kernel graph sat nauty gen rconfig;
PolyML.print_depth 10;

val size = 14;
val m = unzip_mat (random_elem (read44 size));
val matl = sat_solver_edgecl (mat_to_edgecl m) (size+1) (4,5);
fun pairbelowy y = List.tabulate (y,fn x => (x,y));
val edgel = pairbelowy size;
fun mat_to_list mx = map (fn (x,y) => mat_sub (mx,x,y)) edgel; 
val cl = map mat_to_list matl;
val cset =  cl;
val cover = ccover cset;
writel ("ramsey_cone/" ^ szip_mat m) (map ilts cover);

fun switch_color m = mat_tabulate (mat_size m, fn (i,j) => 
  if mat_sub (m,i,j) = 0 then 0 else 3 - mat_sub (m,i,j));

val m449 = unzip_mat (random_elem (read44 9));
val m3510 = unzip_mat (random_elem (read35 10));
val m4410 = unzip_mat (random_elem (read44 10));
val m5311 = switch_color (unzip_mat (random_elem (read35 11)));

*)


end (* struct *)






