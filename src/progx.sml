(* ========================================================================= *)
(* DESCRIPTION   : Extended program datatype to store names for subloops     *)
(* ========================================================================= *)

structure progx :> progx =
struct

open HolKernel Abbrev boolLib aiLib dir kernel
val ERR = mk_HOL_ERR "progx"
type prog = kernel.prog

(* --------------------------------------------------------------------------
   Definition
   -------------------------------------------------------------------------- *)

datatype progx = Insx of ((int * string option) * progx list)

fun progx_compare (Insx(s1,pl1),Insx(s2,pl2)) =
  cpl_compare (cpl_compare Int.compare (option_compare String.compare)) 
    (list_compare progx_compare) ((s1,pl1),(s2,pl2))

fun progx_size (Insx(id,pl)) = 1 + sum_int (map progx_size pl)

fun progx_compare_size (p1,p2) =
  cpl_compare Int.compare 
    progx_compare ((progx_size p1,p1),(progx_size p2,p2))  
 
fun name_progx (s,Insx ((px,no),pxl)) = case no of 
    SOME olds => 
    let val news = s ^ " " ^ olds in 
      Insx ((px,SOME news),pxl) 
    end
  | NONE => Insx ((px,SOME s),pxl)
  
fun unname_progx (Insx ((px,no),pxl)) = (Insx ((px,NONE),pxl)) 
 
fun progx_to_string p = 
  let   
    fun h p = progx_to_string p
    fun sbinop s (p1,p2) = "(" ^ h p1 ^ " " ^ s ^ " " ^ h p2 ^ ")"  
  in
    case p of
      Insx ((0,_),[]) => its 0
    | Insx ((1,_),[]) => its 1
    | Insx ((2,_),[]) => its 2
    | Insx ((3,_),[p1,p2]) => sbinop "+" (p1,p2)
    | Insx ((4,_),[p1,p2]) => sbinop "-" (p1,p2) 
    | Insx ((5,_),[p1,p2]) => sbinop "*" (p1,p2)
    | Insx ((6,_),[p1,p2]) => sbinop "div" (p1,p2)
    | Insx ((7,_),[p1,p2]) => sbinop "mod" (p1,p2)
    | Insx ((8,_),[p1,p2,p3]) => 
      "(if " ^ h p1 ^ " <= 0 then " ^ h p2  ^ " else " ^ h p3 ^ ")"
    | Insx ((id,_),[]) => name_of_oper id
    | Insx ((id,NONE),pl) => 
      "(" ^ String.concatWith " " (name_of_oper id :: map h pl) ^ ")"
    | Insx ((id,SOME s),pl) => 
      "(" ^ String.concatWith " " (name_of_oper id ^ ":" ^ s :: map h pl) ^ ")"  
  end
  
(* --------------------------------------------------------------------------
   Converting between the type progx and prog with and without name sharing
   -------------------------------------------------------------------------- *)

fun progx_to_prog (Insx ((i,_),pl)) = Ins (i, map progx_to_prog pl)
fun progxpair_to_progpair (a,b) = (progx_to_prog a, progx_to_prog b)

fun prog_to_progx_aux i prog = case prog of
    Ins (9,[p1,p2,p3]) =>
    let
      val vs = "v" ^ its (!i)
      val _ = incr i
      val plx = map (prog_to_progx_aux i) [p1,p2,p3]
    in
      Insx ((9,SOME vs),plx)
    end
  | Ins (12,[p1,p2]) => 
    let
      val vs = "v" ^ its (!i)
      val _ = incr i
      val plx = map (prog_to_progx_aux i) [p1,p2]
     in
       Insx ((12,SOME vs),plx)
     end
  | Ins (13,[p1,p2,p3,p4,p5]) => 
    let
      val ws = "w" ^ its (!i)
      val _ = incr i
      val plx = map (prog_to_progx_aux i) [p1,p2,p3,p4,p5]
    in
      Insx ((13,SOME ws),plx)
    end
  | Ins (id,pl) => Insx((id,NONE), map (prog_to_progx_aux i) pl)


fun prog_to_progx_shared_aux i d prog = 
  if dmem prog (!d) then dfind prog (!d) else
  case prog of
    Ins (9,[p1,p2,p3]) =>
    let
      val vs = "v" ^ its (!i)
      val _ = incr i
      val plx = map (prog_to_progx_shared_aux i d) [p1,p2,p3]
      val r = Insx ((9,SOME vs),plx)
    in
      d := dadd prog r (!d); r
    end
  | Ins (12,[p1,p2]) => 
    let
      val vs = "v" ^ its (!i)
      val _ = incr i
      val plx = map (prog_to_progx_shared_aux i d) [p1,p2]
      val r = Insx ((12,SOME vs),plx)
    in
      d := dadd prog r (!d); r
    end
  | Ins (13,[p1,p2,p3,p4,p5]) => 
    let
      val ws = "w" ^ its (!i)
      val _ = incr i
      val plx = map (prog_to_progx_shared_aux i d) [p1,p2,p3,p4,p5]
      val r = Insx ((13,SOME ws),plx)
    in
      d := dadd prog r (!d); r
    end
  | Ins (id,pl) => Insx((id,NONE), map (prog_to_progx_shared_aux i d) pl)

fun prog_to_progx p =
  let val i = ref 0 in prog_to_progx_aux i p end

fun progpair_to_progxpair (p1,p2) =
  let val i = ref 0 in
    (prog_to_progx_aux i p1, prog_to_progx_aux i p2)
  end

fun progpair_to_progxpair_shared (p1,p2) =
  let 
    val i = ref 0 
    val d = ref (dempty prog_compare)
  in
    (prog_to_progx_shared_aux i d p1, prog_to_progx_shared_aux i d p2)
  end

(* --------------------------------------------------------------------------
   Naming arguments of subloops
   -------------------------------------------------------------------------- *)
   
fun progx_to_progxx prog = case prog of
    Insx ((9,SOME vs),[p1,p2,p3]) =>
    let
      val is = tl_string vs
      val argl = map (fn x => x ^ is) ["f","g","h"]
      val plx = map name_progx (combine (argl,map progx_to_progxx [p1,p2,p3]))
    in
      Insx ((9,SOME vs),plx)
    end
  | Insx ((12,SOME vs),[p1,p2]) =>
    let
      val is = tl_string vs
      val argl = map (fn x => x ^ is) ["f","g"]
      val plx = map name_progx (combine (argl,map progx_to_progxx [p1,p2]))
    in
      Insx ((12,SOME vs),plx)
    end
  | Insx ((13,SOME ws),[p1,p2,p3,p4,p5]) => 
    let
      val is = tl_string ws
      val argl = map (fn x => x ^ is) ["f","g","h","i","j"]
      val plx = map name_progx 
        (combine (argl,map progx_to_progxx [p1,p2,p3,p4,p5]))
    in
      Insx ((13,SOME ws),plx)
    end
  | Insx (a,pl) => Insx (a, map progx_to_progxx pl);

(* --------------------------------------------------------------------------
   Collecting subprograms
   -------------------------------------------------------------------------- *)

fun filter_subprog_aux rl test (p as (Insx (a,pl))) =
  (
  app (filter_subprog_aux rl test) pl;
  if test p then rl := p :: !rl else ()
  )

fun filter_subprog test p = 
  let val rl = ref [] in filter_subprog_aux rl test p; !rl end;
  
fun is_loop (Insx ((id,_),_)) = id = 9  
fun all_subloop px = filter_subprog is_loop px

fun is_compr (Insx ((id,_),_)) = id = 12  
fun all_subcompr px = filter_subprog is_compr px

fun is_loop2 (Insx ((id,_),_)) = id = 13  
fun all_subloop2 px = filter_subprog is_loop2 px

fun is_named (Insx ((_,no),_)) = isSome no
fun all_subnamed px = filter_subprog is_named px

fun all_subprog px = filter_subprog (fn _ => true) px

(* --------------------------------------------------------------------------
   Collecting higher-order arguments
   -------------------------------------------------------------------------- *)

fun hoarg_loop px = case px of
    Insx ((9,SOME vs),[p1,p2,p3]) => (p1, tl_string vs)
  | _ => raise ERR "not a loop" ""

fun hoarg_compr px = case px of
    Insx ((12,SOME vs),[p1,p2]) => (p1, tl_string vs)
  | _ => raise ERR "not a compr" ""

fun hoarg_loop2 px = case px of
    Insx ((13,SOME ws),[p1,p2,p3,p4,p5]) => ((p1,p2), tl_string ws)
  | _ => raise ERR "not a loop2" ""  
  
  
end (* struct *)






