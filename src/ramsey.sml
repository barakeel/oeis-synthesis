structure ramsey :> ramsey =
struct

open HolKernel Abbrev boolLib aiLib kernel
val ERR = mk_HOL_ERR "ramsey"

(* -------------------------------------------------------------------------
   Takes the basic array: put the last vertex at index n-1 to index 0
   and index 0 to n-2 maps to 1 to n-1.
   ------------------------------------------------------------------------- *)

fun mk_sym a gsize = 
  let fun f (x,y) = if x = y then false else 
                    if x < y then Array2.sub (a,x,y)
                    else Array2.sub (a,y,x) 
  in
    Array2.tabulate Array2.RowMajor (gsize,gsize,f)
  end

fun invert a gsize =
  let fun f (x,y) = not (Array2.sub (a,x,y)) in
    Array2.tabulate Array2.RowMajor (gsize,gsize,f)
  end
  
(* sigma is a permutation from new indices to old indices *)
fun permute sigma a gsize =
  let fun f (x,y) = Array2.sub (a,sigma x,sigma y) in
    Array2.tabulate Array2.RowMajor (gsize,gsize,f)
  end

(* permutate so that the new vertex have index 0 *)
fun cycle a gsize =
  let fun sigma x = if x = 0 then gsize-1 else x-1 in
    permute sigma a gsize
  end

(* -------------------------------------------------------------------------
   All cliques containing vertex 0
   ------------------------------------------------------------------------- *)

fun is_link a x y = 
  if x >= y then raise ERR "is_link" "should not happen" else
  Array2.sub (a,x,y);

fun all_link a clique y = all (fn x => is_link a x y) clique;
  
(* extend one clique with all potential vertices *)
fun update_clique a n l clique =
  let 
    fun loop y = 
      if y >= n then () else
        (
        if all_link a clique y 
        then l := (y :: clique) :: !l
        else ();
        loop (y+1)
        )
  in
    loop (hd clique + 1)
  end;
  
(* extend all clique with all vertices *)  
fun update_all_clique a n l cliquel = app (update_clique a n l) cliquel;
  
fun all_clique a n size = 
  let
    fun next_cliquel cliquel =
      let val l = ref [] in (update_all_clique a n l cliquel; !l) end
  in
    if size <= 1 then raise ERR "all_clique" "" 
    else funpow (size - 1) next_cliquel [[0]]
  end

(* -------------------------------------------------------------------------
   All cliques containing vertex 0
   ------------------------------------------------------------------------- *)
  
fun contains_clique a gsize size1 size2 = 
  let 
    val aperm = cycle a gsize
    val aanti = invert aperm gsize
    val cliquel = all_clique aperm gsize size1
    val anticliquel = all_clique aanti gsize size2
  in
    not (null cliquel) orelse not (null anticliquel)
  end


fun update_array a f gsize = 
  let 
    fun loop i = 
      if i >= gsize - 1 then () else
      let val b = f (i,gsize-1) in
        Array2.update (a,i,gsize-1,b);
        Array2.update (a,gsize-1,i,b);
        loop (i+1)
      end   
  in
    (loop 0; true)
  end
  handle Div => false | ProgTimeout => false | Overflow => false

fun ramsey f n size1 size2 = 
  let
    val a = Array2.tabulate Array2.RowMajor (n,n,fn _ => false)  
    fun loop gsize = 
      if gsize > n then (a, gsize-1) else
      (
      if not (update_array a f gsize) then (a, gsize-1) 
      else if contains_clique a gsize size1 size2 
        then (a, gsize-1) 
      else loop (gsize + 1)
      )
  in
    loop 1
  end;

(* -------------------------------------------------------------------------
   Graph normalization
   ------------------------------------------------------------------------- *)

fun neighbor_of a gsize x = 
  let 
    val l = ref []
    fun loop y = 
      if y >= gsize then ()
      else (if Array2.sub (a,x,y) orelse x = y 
            then l := y :: !l else (); 
            loop (y + 1))
  in
    loop 0; 
    mk_fast_set Int.compare (!l)
  end
  
fun all_neighbor a gsize =
  Vector.tabulate (gsize, fn x => neighbor_of a gsize x)

fun charac nv a gsize x =
  let
    val l = ref []
    fun loop nl = 
      let 
        val nll = map (fn y => Vector.sub (nv,y)) nl
        val newnl = mk_fast_set Int.compare (List.concat nll) 
      in
        if newnl = nl then () else
        (l := length newnl :: !l; loop newnl)
      end
  in
    loop [x]; rev (!l)
  end
    
fun all_charac a gsize =
  let val nv = all_neighbor a gsize in
    List.tabulate (gsize, fn x => (x, charac nv a gsize x))   
  end

fun norm_graph a gsize =
  let
    val cl = all_charac a gsize
    val clsorted = dict_sort (snd_compare (list_compare Int.compare)) cl
    val cv = Vector.fromList (map fst clsorted)
    fun sigma x = Vector.sub (cv,x)
  in
    permute sigma a gsize
  end

end (* struct *)

(* -------------------------------------------------------------------------
   Test
   ------------------------------------------------------------------------- *)

(*
load "ramsey"; open ramsey;
load "aiLib"; open aiLib;
val gsize = 36;
fun frandom (a,b) = random_int (0,1);
fun fglob () = ramsey frandom n 4 6;

val (abest,nbest) = 
  hd (dict_sort compare_imax  (List.tabulate (20000,fn _ => fglob ())));
*)

(*
load "ramsey"; open ramsey;
load "aiLib"; open aiLib;
val gsize = 8;
val a = Array2.tabulate Array2.RowMajor 
  (gsize,gsize,fn _ => random_real () < 0.5);
val asym = mk_sym a gsize;

val charac = all_charac asym gsize;
val anorm = norm_graph asym gsize;
val characnorm = all_charac anorm gsize;

*)
