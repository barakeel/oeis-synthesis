laod "kernel"; open aiLib kernel;

fun is_faster (t1,p1) (t2,p2) =   
  cpl_compare Int.compare prog_compare_size ((t1,p1),(t2,p2)) = LESS

fun is_smaller (t1,p1) (t2,p2) = prog_compare_size (p1,p2) = LESS;

fun fgen i =
  let 
    val sol = read_itprogl (selfdir ^ "/exp/bothfs/hist/itsol" ^ its i) 
    val small = ref []
    val fast = ref []
    fun f (anum,tpl) = case tpl of
      [a,b] => 
        let 
          val fastp = if is_faster a b then a else b
          val smallp = if is_smaller a b then a else b
        in
          if equal_prog (snd fastp, snd smallp) then raise ERR "fgen" "" else ();
          small := smallp :: !small;
          fast := fastp :: !fast
        end
      | _ => ()
    val _ = app f sol 
    val sizesmall = average_int (map (prog_size o snd) (!small))
    val sizefast = average_int (map (prog_size o snd) (!fast))
    val speedsmall = average_int (map fst (!small))
    val speedfast = average_int (map fst (!fast))
  in
    (i, length sol, length (!small), length (!fast), 
     sizesmall, sizefast, speedsmall, speedfast) 
  end;

val rl = List.tabulate (210,fgen);


fun fgensol (a,b,c,d,_,_,_,_) = String.concatWith " " (map its [a,b,c,d])
fun fgensize (a,b,c,d,e,f,_,_) = 
  its a ^ " " ^ rts_round 4 e ^ " " ^ rts_round 4 f;
fun fgenspeed (a,b,c,d,e,f,g,h) = 
  its a ^ " " ^ rts_round 2 g ^ " " ^ rts_round 2 h;
writel "smt/gensol" ("gen sol solsmall solfast" :: map fgensol rl);
writel "smt/gensize" ("gen sizesmall sizefast" :: map fgensize rl);
writel "smt/genspeed" ("gen speedsmall speedfast" :: map fgenspeed rl);
