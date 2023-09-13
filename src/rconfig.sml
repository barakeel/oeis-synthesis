structure rconfig :> rconfig =
struct   

open HolKernel Abbrev boolLib aiLib kernel
val ERR = mk_HOL_ERR "rconfig"

(* -------------------------------------------------------------------------
   Config file
   ------------------------------------------------------------------------- *)

val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)

val ramseyconfigd = 
  if exists_file (selfdir ^ "/ramsey_config") then 
    let 
      val sl = readl (selfdir ^ "/ramsey_config")
      fun f s = SOME (pair_of_list (String.tokens Char.isSpace s)) 
        handle HOL_ERR _ => NONE
    in
      dnew String.compare (List.mapPartial f sl)
    end
  else dempty String.compare

fun bflag s b = 
  string_to_bool (dfind s ramseyconfigd) handle NotFound => b
fun iflag s i = 
  string_to_int (dfind s ramseyconfigd) handle NotFound => i
fun rflag s r = 
  valOf (Real.fromString (dfind s ramseyconfigd)) handle NotFound => r

val real_time = rflag "real_time" 0.0
val abstract_time = iflag "abstract_time" 0
val memory = iflag "memory" 10000



  
end (* struct *)

(*
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 10;
*)


