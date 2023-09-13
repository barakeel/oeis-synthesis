load  "aiLib"; open aiLib;

fun suffix n s = String.substring (s,n,String.size s - n);

fun mkgraphnocut file =
  let 
    val id = suffix 3 (OS.Path.file file)
    val fileout = "graphnocut/graph" ^ id
    val l0 = readl file;
    val l1 = filter (String.isPrefix "solutions:") l0
    fun f x = string_to_int (last (String.tokens Char.isSpace x))
    val l2 = number_fst 0 (map f l1)
    fun g (a,b) = its a ^ " " ^ its b
  in
    mkDir_err "graphnocut";
    writel fileout ("gen sol" :: (map g l2))
  end;
  
val filel = map (fn x => "log/" ^ x) (listDir "log");
app mkgraphnocut filel;
  
val l0 = readl "log/logsmallandfast";
val l1 = filter (String.isPrefix "solutions:") l0;
val l2 = first_n 210 l1;
val l0' = readl "log/loglongrun";
val l1' = filter (String.isPrefix "solutions:") l0';
val l3 = l2 @ l1';
fun f x = string_to_int (last (String.tokens Char.isSpace x));
val l4 = number_fst 0 (map f l3);
fun g (a,b) = its a ^ " " ^ its b;
writel "graphlongrun" (map g l4);


fun mktable () =
  let 
    val filel = map (fn x => "log/" ^ x) (listDir "log");
    fun ff file =
      let 
        val id = suffix 3 (OS.Path.file file)
        val fileout = "graphnocut/graph" ^ id
        val l0 = readl file;
        val l1 = filter (String.isPrefix "solutions:") l0
        fun f x = string_to_int (last (String.tokens Char.isSpace x))
        val l2 = number_fst 0 (map f l1)
        val l3 = filter (fn (a,b) => a <= 20 andalso a mod 5 = 0) l2
        val l4 = map snd l3
      in
        (id,l4)
      end
    fun gg (id,l) = String.concatWith " & " (id :: map its l) ^ "\\\\"
  in
    writel "atable" (map (gg o ff) filel)
  end;
  

load "aiLib"; open aiLib; 
load "kernel"; open kernel;


val allsol = l

fun f i = 
  (
  print_endline (its i);
  read_itprogl 
    ("/home/mptp/nfs/OEIS_Programs_full/run1/exp" ^ its i ^ "-chk/solold")
  );   
    
PolyML.print_depth 2;  
val allsol = map f (List.tabulate (187,fn x => x + 2));
 
val file = "/home/mptp/nfs/OEIS_Programs_full/run1/exp100-chk/solold";  
val sol = time read_itprogl  file;
fun get_mintime (a,l) = list_imin (map fst l);
val mintimel = map get_mintime sol;
val tim = average_int mintimel;
fun get_minsize (a,l) = list_imin (map (prog_size o snd) l);
val minsizel = map get_minsize sol;

val size = sum_int minsizel;  
val size = average_int minsizel;  


val dtime = ref (dempty Int.compare)
fun update_dtime x = 
  let 
    val k = fst x 
    val v = get_minsize x
    val oldl = dfind k (!dtime) handle NotFound => []
  in
    dtime := dadd k (v :: oldl) (!dtime)
  end;

fun get_mintime (a,l) = list_imin (map fst l);
fun get_minsize (a,l) = list_imin (map (prog_size o snd) l);

val allsollin = List.concat allsol;

fun compression filename ff =
  let
    val d = ref (dempty Int.compare)
    fun g x = 
      let 
        val k = fst x 
        val v = ff x
        val oldl = dfind k (!d) handle NotFound => []
      in
        d := dadd k (v :: oldl) (!d)
      end
    val _ = app g allsollin
    val (l0 : int list list) = map snd (dlist (!d))
    val l1 = filter (fn x => length x >= 100) l0
    val l2 = map (first_n 100 o rev) l1
    val l3 = list_combine l2
    val l4 = map average_int l3
  in
    writel filename (map rts l4)
  end;
  
compression "time_compression" get_mintime; 
compression "size_compression" get_minsize;
  



 
