structure satenc :> satenc =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph rconfig
val ERR = mk_HOL_ERR "satenc"

(* -------------------------------------------------------------------------
   Variable names
   ------------------------------------------------------------------------- *)

fun E a b = "E" ^ its a ^ "-" ^ its b
fun X i = "X" ^ its i;
fun S i j = "S" ^ its i ^ "-" ^ its j;
fun F s = (s,false)
fun T s = (s,true)

(* -------------------------------------------------------------------------
   Ramsey clauses
   ------------------------------------------------------------------------- *)

fun clique_of_subset (subset,color) =
  let 
    val pairl = all_pairs (dict_sort Int.compare subset) 
    fun f (a,b) = (E a b, color <> blue)
  in
    map f pairl
  end

fun ramsey_clauses size (bluesize,redsize) = 
  let
    val vertexl = List.tabulate (size,I)
    val bluesubsetl = subsets_of_size bluesize vertexl
    val redsubsetl = subsets_of_size redsize vertexl
    val subsetl = map_assoc (fn _ => blue) bluesubsetl @
                  map_assoc (fn _ => red) redsubsetl
  in
    map clique_of_subset subsetl
  end

(* -------------------------------------------------------------------------
   Degree clauses
   ------------------------------------------------------------------------- *)

fun atmostk1 n = range (1, n-1, fn i => [F (X i), T (S i 1)]);
fun atmostk2 k = range (2,k, fn j => [F (S 1 j)])
fun atmostk3 k n = List.concat (
  range (2,n-1, fn i => range (1,k, fn j => 
    [F (S (i-1) j), T (S i j)])));   
fun atmostk4 k n = List.concat (
  range (2,n-1, fn i => range (2,k, fn j => 
    [F (S (i-1) (j-1)), F (X i), T (S i j)])));
fun atmostk5 k n = 
  range (2,n, fn i => [F (S (i-1) k), F (X i)]);

fun atmostk k n = List.concat 
  [atmostk1 n, atmostk2 k, atmostk3 k n, atmostk4 k n, atmostk5 k n]

fun atleastk k n = 
  let fun f (x,b) = if String.isPrefix "X" x then (x,not b) else (x,b) in
    map (map f) (atmostk (n-k) n)
  end
  
fun atmostk_named k vl sprefix =
  let 
    val n = length vl
    val Xl = List.tabulate (n, fn i => X (i+1));   
    val d = dnew String.compare (combine (Xl,vl))
    fun f x = if String.isPrefix "X" x then dfind x d else sprefix ^ x
  in
    map (map_fst f) (atmostk k n)
  end
  
fun atleastk_named k vl sprefix =
  let 
    val n = length vl
    val Xl = List.tabulate (n, fn i => X (i+1));   
    val d = dnew String.compare (combine (Xl,vl))
    fun f x = if String.isPrefix "X" x then dfind x d else sprefix ^ x
  in
    map (map_fst f) (atleastk k n)
  end

fun edges_of_vertex vertexl v = 
  let 
    fun f w = if v = w then NONE else 
      if v < w then SOME (v,w) else SOME (w,v)
    fun g (a,b) = E a b
  in
    map g (List.mapPartial f vertexl)
  end

fun cdeg size csize (mindeg,maxdeg) =
  let val vertexl = List.tabulate (size,I) in
    List.concat 
    (List.tabulate (csize, fn v =>
    let 
      val edgel = edges_of_vertex vertexl v
      val vl = atleastk_named mindeg edgel ("VL" ^ its v ^ "_")
      val vm = atmostk_named maxdeg edgel ("VM" ^ its v  ^ "_")
    in
      vl @ vm
    end))
  end

fun ddeg size csize (mindeg,maxdeg) = 
  let val vertexl = List.tabulate (size,I) in
    List.concat 
    (range (csize,size-1, fn v =>
    let 
      val edgel = edges_of_vertex vertexl v
      val vl = atleastk_named mindeg edgel ("VL" ^ its v ^ "_")
      val vm = atmostk_named maxdeg edgel ("VM" ^ its v  ^ "_")
    in
      vl @ vm
    end)) 
  end
  

(* -------------------------------------------------------------------------
   Problem without assignment clauses
   ------------------------------------------------------------------------- *)

fun write_clauses file clauses = 
  let 
    fun g (x,c) = if c then its x else "-" ^ its x
    fun f clause = String.concatWith " " (map g clause) ^ " 0"
  in
    writel file (map f clauses)
  end
   
fun write_pb file pb =
  let
    val allvar = mk_fast_set String.compare (List.concat (map (map fst) pb));
    val vard = dnew String.compare (number_snd 1 allvar);
    val pbnumbered = map (map_fst (fn x => dfind x vard)) pb;
    fun test (s,i) = String.isPrefix "E" s
    fun f (s,i) = s ^ " " ^ its i
    val header = its (dlength vard) ^ " " ^ its (length pbnumbered)
    val mapping = map f (filter test (dlist vard))
  in
    writel (file ^ "_mapping") (header :: mapping);
    write_clauses (file ^ "_clauses") pbnumbered
  end   

fun write_r45_pb file =
  let
    val size = 24
    val ram = ramsey_clauses size (4,5)
  in 
    write_pb file ram
  end  

fun write_r45_pb_wdeg csize (mindeg,maxdeg) file =
  let
    val size = 24
    val ram = ramsey_clauses size (4,5)
    val deg1 = cdeg size csize (mindeg-1,maxdeg-1)
    val deg2 = ddeg size csize (mindeg,maxdeg)
  in 
    write_pb file (ram @ deg1 @ deg2)
  end  

fun write_pb_10_14 file =
  let
    val size = 24
    val csize = 10
    val ram = ramsey_clauses size (4,5)
    val deg1 = cdeg size csize (9,10)
    val deg2 = ddeg size csize (10,11)
  in 
    write_pb file (ram @ deg1 @ deg2)
  end

fun read_mapping file = 
  let 
    val sl = readl (file ^ "_mapping")
    val (nvar,nclause) = pair_of_list 
      (map string_to_int (String.tokens Char.isSpace (hd sl)))
    fun f s = 
      let val (s1,s2) = pair_of_list (String.tokens Char.isSpace s) in
        (s1, string_to_int s2)
      end
    val vard = dnew String.compare (map f sl)
  in
    ((nvar,nclause),vard)
  end
  
(* -------------------------------------------------------------------------
   Assignment clauses
   ------------------------------------------------------------------------- *)

fun edgecl_clauses edgecl = 
  let 
    fun f ((i,j),color) = 
      if color = 1 then (E i j, true)
      else if color = 2 then (E i j, false)
      else raise ERR "edgecl_clauses" ""
  in 
    map (fn x => [x]) (map f edgecl)
  end
  
fun write_assignl_aux file header vard edgecl = 
  let 
    val pb1 = edgecl_clauses edgecl
    val pb2 = map (map_fst (fn x => dfind x vard)) pb1
    fun g (x,c) = if c then its x else "-" ^ its x
    fun f clause = String.concatWith " " (map g clause) ^ " 0"
  in
    writel file (header :: map f pb2)
  end

fun write_assignl file ((nvar,nclause),vard) pbid (ce,de) = 
  let
    val csize = mat_size ce
    val edgecl = mat_to_edgecl ce @ 
      map_fst (fn (a,b) => (a+csize,b+csize)) (mat_to_edgecl de)
    val file = file ^ "_assign_" ^ pbid
    val header = "p cnf " ^ its nvar ^ " " ^ its (nclause + length edgecl)
  in           
    write_assignl_aux file header vard edgecl
  end


end (* struct *)

(*
PolyML.print_depth 0;
load "satenc"; load "ramsey"; open aiLib kernel graph satenc ramsey;
PolyML.print_depth 10;


val pb = ramsey_clauses 24 (4,5) @ edgecl_clauses (ecl44 @ ecl35);
val file = "aatest";
write_pb file pb;

val file = "r45_10-14";
write_pb_10_14 file;

val ci = random_elem (read35 10);  
val ce = unzip_mat ci;  
val di = random_elem (read44 14);  
val de = unzip_mat di;  
 
val x = read_mapping file;

write_assignl "r45_10-14" x (ce,de);


*)


